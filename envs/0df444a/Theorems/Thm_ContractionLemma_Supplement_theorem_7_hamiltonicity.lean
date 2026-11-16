-- Prove2me | Theorems.Thm_ContractionLemma_Supplement_theorem_7_hamiltonicity
-- name    : ContractionLemma.Supplement.theorem_7_hamiltonicity
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:24:58.643234+00:00
-- url     : https://prove2.me/theorems/fecb12fe-0c83-47ea-92c4-b7f8b02ad67e
-- title:
--   Theorem 7, p.28 — Hamiltonian path and cycle, and their minimum-cost versions, in randomized time $\mathrm{poly}(L)\log(1/\delta)E(\sigma(n,m))$
-- statement:
--   Let $\sigma(n,m)=n\cdot\max\{1,\log(m/n)\}$. For Hamiltonian paths and for Hamiltonian cycles, on simple directed or undirected graphs with $n$ vertices and $m$ edges, given the graph and a rational error bound $0<\delta<1$ (input length $L$), there are randomized algorithms running in time
--
--   $$
--   C(L+1)^C\,\bigl(1+\log_2(1/\delta)\bigr)\,2^{C\sigma(n,m)/\sqrt{\log_2(\sigma(n,m)+2)}}
--   $$
--
--   and space $C(L+1)^C$ with one-sided error $\delta$:
--
--   1. a decision algorithm that never accepts a graph without a Hamiltonian path (cycle), and rejects a graph that has one with probability at most $\delta$;
--   2. a search algorithm that always outputs "none" or a genuine Hamiltonian path (cycle), and outputs "none" on a graph that has one with probability at most $\delta$;
--   3. for every constant $c$, on graphs with integer costs of at most $c\,n^{3/4}$ bits, an algorithm that always outputs "none" or a genuine Hamiltonian path (cycle), and with probability at least $1-\delta$ outputs one of minimum cost whenever one exists.
--
--   For graphs with $O(n)$ edges this is randomized time $2^{O(n/\sqrt{\log n})}$, which gives subexponential TSP on sparse graphs (Corollary 8).
--
--   Differences from the source:
--   - reading: the factor $\log(1/\delta)$ → $1+\log_2(1/\delta)$; reason: $\log(1/\delta)$ tends to $0$ as $\delta\to1$; the paper means $O(\log(1/\delta))$ repetitions, at least one
--   - reading: "randomized time … with one-sided error $\delta$" → a machine that reads fair coins one at a time on request (one step and one visited cell per coin; `RandRunsWithin`); forbidden outputs never occur, and the wrong-answer probability over the coin string is at most $\delta$; reason: Lean model of randomized algorithms, the coin model of §2.5 (p.20)
--   - reading: no space bound in the theorem sentence → space at most $C(L+1)^C$ (polynomial in the input length); reason: the paper's convention, p.3: "all algorithms are deterministic and use polynomial space unless we say otherwise"
--   - encoding: graphs; Hamiltonian cycles → simple graphs as arc lists with one cost per arc; a cycle has at least two vertices (directed) or three (undirected); reason: p.29: "for $n=2$ the two orientations of one edge form a directed cycle that is not a cycle of the undirected graph"
--   - encoding: $O(\cdot)$, $\mathrm{poly}(\cdot)$, $E(u)=2^{O(u/\sqrt{\log u})}$ → explicit constants fixed before the instance; $E(u)=2^{C f(u)}$, $f(u)=u/\sqrt{\log_2(u+2)}$; reason: the paper's own $f$ (p.16); log base two
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Theorem 7, p.28 (stated first on p.7); §6, pp.29–32

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_RunsWithin
import Definitions.Def_ContractionLemma_Supplement_Common
import Definitions.Def_ContractionLemma_Supplement_Problems
import Definitions.Def_ContractionLemma_Supplement_Reduction

set_option autoImplicit false

namespace ContractionLemma.Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open scoped Classical
/-- **Theorem 7 (Hamiltonicity)** — Gajulapalli, *The Contraction Lemma Beyond ETH* (manuscript,
sha256 049caea1…), p.28 (PDF p.31; stated first on p.7).

"Hamiltonian path and Hamiltonian cycle, on directed or undirected graphs with `n` vertices and `m`
edges, can be decided, and a witness found, in randomized time `poly(L) log(1/δ) E(σ(n, m))` with
one-sided error `δ`. Minimum-cost Hamiltonian path and cycle, with integer costs of `O(n^{3/4})` bits,
have the same bound."

For Hamiltonian paths (`closed = false`) and cycles (`closed = true`), on simple directed or
undirected graphs, there are randomized machines and a constant `C` such that on input
`(G, δ)`, `0 < δ < 1` (length `L`), each runs in time `C (L+1)^C (1 + log₂(1/δ)) 2^{C f(σ(n,m))}`
and space `C (L+1)^C`, with `σ(n,m) = n·max{1, log(m/n)}`, and:

1. the decision machine never accepts a graph without a Hamiltonian path/cycle and rejects one that
   has it with probability at most `δ`;
2. the search machine always outputs `none` or a genuine Hamiltonian path/cycle, and outputs `none`
   on a graph that has one with probability at most `δ`;
3. for every `c`, on graphs whose costs have at most `c·n^{3/4}` bits, the minimum-cost machine
   always outputs `none` or a genuine Hamiltonian path/cycle, and with probability at least `1 − δ`
   outputs one of minimum cost when one exists.

**Formalization Note.** Randomness is the coin model of §2.5 (`RandRunsWithin`): the algorithm is a
machine that requests fair coins one at a time (an oracle step with an empty query); each coin costs
one step and one visited cell, and the error probability is over the coin string.
`log(1/δ)` is read as `1 + log₂(1/δ)` so that the bound stays positive for `δ` near `1`. `f(u) =
u/√log₂(u+2)`. The polynomial-space clause is the paper's convention (p.3). -/
theorem theorem_7_hamiltonicity (closed : Bool) :
    (∃ (A : OracleMachine) (out : Fin A.machine.tapeCount) (C : ℕ), ∀ (H : HamInst) (δ : ℚ),
      0 < δ → δ < 1 →
      A.RandRunsWithin out (Encoding.encodeList id [H.encode, ratWord δ])
        (C * (((Encoding.encodeList id [H.encode, ratWord δ]).length : ℝ) + 1) ^ C *
          (1 + Real.logb 2 (1 / (δ : ℝ))) * (2 : ℝ) ^ (C * fScale H.sigma))
        (C * (((Encoding.encodeList id [H.encode, ratWord δ]).length : ℝ) + 1) ^ C)
        (fun y => y = [false] ∨ (y = [true] ∧ ∃ P, H.IsHam closed P))
        (fun y => y = [decide (∃ P, H.IsHam closed P)]) δ) ∧
    (∃ (A : OracleMachine) (out : Fin A.machine.tapeCount) (C : ℕ), ∀ (H : HamInst) (δ : ℚ),
      0 < δ → δ < 1 →
      A.RandRunsWithin out (Encoding.encodeList id [H.encode, ratWord δ])
        (C * (((Encoding.encodeList id [H.encode, ratWord δ]).length : ℝ) + 1) ^ C *
          (1 + Real.logb 2 (1 / (δ : ℝ))) * (2 : ℝ) ^ (C * fScale H.sigma))
        (C * (((Encoding.encodeList id [H.encode, ratWord δ]).length : ℝ) + 1) ^ C)
        (fun y => y = optWord none ∨ ∃ P, H.IsHam closed P ∧ y = optWord (some (pathWord P)))
        (fun y => (∃ P, H.IsHam closed P) → ∃ P, H.IsHam closed P ∧ y = optWord (some (pathWord P)))
        δ) ∧
    (∀ c : ℕ, ∃ (A : OracleMachine) (out : Fin A.machine.tapeCount) (C : ℕ), ∀ (H : HamInst) (δ : ℚ),
      0 < δ → δ < 1 → (∀ z ∈ H.cost, (z.natAbs.size : ℝ) ≤ c * (H.n : ℝ) ^ ((3 : ℝ) / 4)) →
      A.RandRunsWithin out (Encoding.encodeList id [H.encode, ratWord δ])
        (C * (((Encoding.encodeList id [H.encode, ratWord δ]).length : ℝ) + 1) ^ C *
          (1 + Real.logb 2 (1 / (δ : ℝ))) * (2 : ℝ) ^ (C * fScale H.sigma))
        (C * (((Encoding.encodeList id [H.encode, ratWord δ]).length : ℝ) + 1) ^ C)
        (fun y => y = optWord none ∨ ∃ P, H.IsHam closed P ∧ y = optWord (some (pathWord P)))
        (fun y => (∃ P, H.IsHam closed P) → ∃ P, H.IsHam closed P ∧
          (∀ P', H.IsHam closed P' → H.pathCost closed P ≤ H.pathCost closed P') ∧
          y = optWord (some (pathWord P)))
        δ) := by sorry

end ContractionLemma.Supplement

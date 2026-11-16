-- Prove2me | Theorems.Thm_ContractionLemma_Supplement_theorem_8_2_oracle_short_queries
-- name    : ContractionLemma.Supplement.theorem_8_2_oracle_short_queries
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:27:11.728037+00:00
-- url     : https://prove2.me/theorems/ff9260e2-fe56-4544-8845-03aefd575fbb
-- title:
--   Theorem 8.2, p.38 — oracle machines with queries of length $O(T^{9/10})$ simulated in time $\mathrm{poly}(T+L)2^{O(T/\sqrt{\log T})}$
-- statement:
--   Let $A$ be an oracle decidable in time $2^{O(m)}$ and space $\mathrm{poly}(m)$ on $m$-bit queries, and fix the parameters of local machines and a constant $c'$. For an oracle machine $M$ with at most $(T+2)^{C_0}$ states running for $T\ge2$ steps, all of whose queries have length at most $c'\,T^{9/10}$, the number of accepting coin strings and the number of accepting nondeterministic paths with oracle $A$ can be computed deterministically in time
--
--   $$
--   \mathrm{poly}(T+L)\;2^{O(T/\sqrt{\log T})}
--   $$
--
--   and polynomial space, where $L$ is the description length. The oracle may be slow: because the queries are short, each is answered inside one block of the simulation.
--
--   Differences from the source:
--   - encoding: oracle machines of §2.5 → an oracle step reads the maximal block of bit symbols at the start of the query tape and moves to one of two states; reason: Lean model of "an oracle step reads a delimited prefix of the query tape"
--   - encoding: $O(\cdot)$, $\mathrm{poly}(\cdot)$, $E(u)=2^{O(u/\sqrt{\log u})}$ → explicit constants fixed before the instance; $E(u)=2^{C f(u)}$, $f(u)=u/\sqrt{\log_2(u+2)}$; reason: the paper's own $f$ (p.16); log base two
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Theorem 8.2, p.38

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_RunsWithin
import Definitions.Def_ContractionLemma_Supplement_Common
import Definitions.Def_ContractionLemma_Supplement_LocalMachine
import Definitions.Def_ContractionLemma_Supplement_Quantum
import Definitions.Def_ContractionLemma_Supplement_Classes

set_option autoImplicit false

namespace ContractionLemma.Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Theorem 8.2 (Oracle machines with short queries)** — Gajulapalli, *The Contraction Lemma
Beyond ETH* (manuscript, sha256 049caea1…), p.38 (PDF p.41).

"Let `A` be an oracle decidable in time `2^{O(m)}` and space `poly(m)` on `m`-bit queries. For an
oracle machine running for `T` steps whose queries have length `O(T^{9/10})`, the number of accepting
coin strings and the number of accepting nondeterministic paths can be computed in time
`poly(T + L) 2^{O(T/√log T)}` and polynomial space."

For every choice of the parameters `(k, Γ, d₀, C₀)`, every oracle `A` decidable in time `2^{O(m)}`
and space `poly(m)`, and every constant `c'`, there are machines and a constant `C` such that for
every oracle program `M` with at most `(T+2)^{C₀}` states, inputs `x`, `aux` and `T ≥ 2` such that
every query of the run has length at most `c' T^{9/10}`, given `(M, x, aux, T)` (length `L`), they
output the number of accepting coin strings, respectively of accepting nondeterministic paths, with
oracle `A`, in time `C (T+L+1)^C 2^{C f(T)}` and space `C (T+L+1)^C`.

**Formalization Note.** Oracle steps follow §2.5: the delimited query is the maximal block of bit
symbols at the start of the query tape; the reply goes into the state. `f(T) = T/√log₂(T+2)`. -/
theorem theorem_8_2_oracle_short_queries (p : LocalParams) (A : Lang) (hA : ExpTimePolySpace A)
    (c' : ℕ) :
    (∃ (S : PrimitiveMachine) (out : Fin S.tapeCount) (C : ℕ),
      ∀ (M : LProgram p) (x aux : List Bool) (T : ℕ), 2 ≤ T → M.Q ≤ (T + 2) ^ p.C0 →
        M.QueriesBounded A x aux T (c' * (T : ℝ) ^ ((9 : ℝ) / 10)) →
        ContractionLemma.RunsWithin S out (M.simInput x aux T) (countWord (M.coinCount A x aux T))
          (C * ((T : ℝ) + (M.simInput x aux T).length + 1) ^ C * (2 : ℝ) ^ (C * fScale T))
          (C * ((T : ℝ) + (M.simInput x aux T).length + 1) ^ C)) ∧
    (∃ (S : PrimitiveMachine) (out : Fin S.tapeCount) (C : ℕ),
      ∀ (M : LProgram p) (x aux : List Bool) (T : ℕ), 2 ≤ T → M.Q ≤ (T + 2) ^ p.C0 →
        M.QueriesBounded A x aux T (c' * (T : ℝ) ^ ((9 : ℝ) / 10)) →
        ContractionLemma.RunsWithin S out (M.simInput x aux T) (countWord (M.pathCount A x aux T))
          (C * ((T : ℝ) + (M.simInput x aux T).length + 1) ^ C * (2 : ℝ) ^ (C * fScale T))
          (C * ((T : ℝ) + (M.simInput x aux T).length + 1) ^ C)) := by sorry

end ContractionLemma.Supplement

-- Prove2me | Theorems.Thm_ContractionLemma_Supplement_theorem_4_dnf_minimization
-- name    : ContractionLemma.Supplement.theorem_4_dnf_minimization
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:23:23.923983+00:00
-- url     : https://prove2.me/theorems/f4f98814-4d24-4ba8-975d-37fef20cbcd7
-- title:
--   Theorem 4, p.26 — minimum DNF by term count or literal count in time $\mathrm{poly}(N)E(I)$
-- statement:
--   Let $f:\{0,1\}^k\to\{0,1\}$ be given by its truth table of $N=2^k$ bits, let $P_1,\dots,P_p$ be its prime implicants, and let
--
--   $$
--   I=\sum_j |P_j^{-1}(1)|
--   $$
--
--   be the number of pairs of a prime implicant and a row that it covers. Then a DNF computing $f$ with the minimum number of terms, and a DNF computing $f$ with the minimum number of literals, can each be constructed deterministically in time $\mathrm{poly}(N)\,E(I)$ and polynomial space, that is, in time $C(N+1)^C\,2^{C I/\sqrt{\log_2(I+2)}}$ and space $C(N+1)^C$ for an absolute constant $C$.
--
--   The scale is the number of incidences between primes and rows, not the number of rows times the number of primes.
--
--   Differences from the source:
--   - reading: no space bound in the theorem sentence → space at most $C(L+1)^C$ (polynomial in the input length); reason: the paper's convention, p.3: "all algorithms are deterministic and use polynomial space unless we say otherwise"
--   - encoding: a truth table; a term in $\{0,1,*\}^k$ → row $x$ at index $\sum_i x_i 2^i$; a DNF is a list of patterns, minimal among all DNFs computing $f$; reason: Lean conventions for the table and the output
--   - encoding: $O(\cdot)$, $\mathrm{poly}(\cdot)$, $E(u)=2^{O(u/\sqrt{\log u})}$ → explicit constants fixed before the instance; $E(u)=2^{C f(u)}$, $f(u)=u/\sqrt{\log_2(u+2)}$; reason: the paper's own $f$ (p.16); log base two
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Theorem 4, p.26 (stated first on p.5); §4.2, pp.25–26

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_RunsWithin
import Definitions.Def_ContractionLemma_Supplement_Common
import Definitions.Def_ContractionLemma_Supplement_Problems

set_option autoImplicit false

namespace ContractionLemma.Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Theorem 4 (DNF minimization)** — Gajulapalli, *The Contraction Lemma Beyond ETH* (manuscript,
sha256 049caea1…), p.26 (PDF p.29; stated first on p.5).

"Given the `N`-bit truth table of a function with prime implicants `P_1, …, P_p`, let
`I = ∑_j |P_j^{−1}(1)|` be the number of pairs of a prime implicant and a row that it covers. A DNF of
minimum term count, or of minimum literal count, can be constructed in time `poly(N) E(I)`."

There are machines and a constant `C` such that, for every `k` and every truth table `tt` of
`f : {0,1}^k → {0,1}` (`N = 2^k` bits), one machine outputs a DNF computing `f` with the minimum
number of terms, and the other a DNF computing `f` with the minimum number of literals, each in time
`C (N+1)^C 2^{C f(I)}` (`f(I) = I/√log₂(I+2)`) and space `C (N+1)^C`.

**Formalization Note.** Row `x ∈ {0,1}^k` of the table is entry `∑_i x_i 2^i`. A term is a pattern
in `{0, 1, ∗}^k`; minimality is over all DNFs computing `f`. The polynomial-space clause is the
paper's convention (p.3). -/
theorem theorem_4_dnf_minimization :
    (∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (C : ℕ), ∀ (k : ℕ) (tt : List Bool),
      tt.length = 2 ^ k → ∃ D : List (Term k), DNFComputes (ttFun tt k) D ∧
        (∀ D' : List (Term k), DNFComputes (ttFun tt k) D' → D.length ≤ D'.length) ∧
        ContractionLemma.RunsWithin A out tt (dnfWord D)
          (C * ((tt.length : ℝ) + 1) ^ C * (2 : ℝ) ^ (C * fScale (primeIncidence (ttFun tt k))))
          (C * ((tt.length : ℝ) + 1) ^ C)) ∧
    (∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (C : ℕ), ∀ (k : ℕ) (tt : List Bool),
      tt.length = 2 ^ k → ∃ D : List (Term k), DNFComputes (ttFun tt k) D ∧
        (∀ D' : List (Term k), DNFComputes (ttFun tt k) D' → litCount D ≤ litCount D') ∧
        ContractionLemma.RunsWithin A out tt (dnfWord D)
          (C * ((tt.length : ℝ) + 1) ^ C * (2 : ℝ) ^ (C * fScale (primeIncidence (ttFun tt k))))
          (C * ((tt.length : ℝ) + 1) ^ C)) := by sorry

end ContractionLemma.Supplement

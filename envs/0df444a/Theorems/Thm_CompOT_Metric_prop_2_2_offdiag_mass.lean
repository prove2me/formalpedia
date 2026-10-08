-- Prove2me | Theorems.Thm_CompOT_Metric_prop_2_2_offdiag_mass
-- name    : CompOT.Metric.prop_2_2_offdiag_mass
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:21.031587+00:00
-- url     : https://prove2.me/theorems/434ca463-8381-4224-a8fe-5e18148e65d6
-- title:
--   Proof of Proposition 2.2, pp. 377–378 — if a ≠ b, every coupling in U(a, b) has a nonzero off-diagonal entry
-- statement:
--   Let $a,b\in\Sigma_n$ with $a\ne b$, and let $P\in U(a,b)$. Then $P$ has a nonzero element outside the diagonal:
--   $$\exists\, i\ne j:\quad P_{i,j}\ne 0.$$
--
--   This is the combinatorial half of the positivity of $\mathrm W_p(a,b)$ for $a\ne b$: a coupling supported on the diagonal has equal row and column sums, so it only couples a histogram with itself.
--
--   **Formalization Note** Indices are `Fin n`.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), proof of Proposition 2.2, pp. 377–378

import Mathlib
import Definitions.Def_CompOT_Metric_Defs

namespace CompOT.Metric

open Matrix

/-- Proof of Proposition 2.2, pp. 377–378: if `a ≠ b`, an admissible coupling
`P ∈ U(a, b)` necessarily has a nonzero element outside the diagonal. -/
theorem prop_2_2_offdiag_mass {n : ℕ} (a b : Fin n → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin n)) (hab : a ≠ b)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P ∈ CompOT.Assignment.couplings a b) :
    ∃ i j, i ≠ j ∧ P i j ≠ 0 := by sorry

end CompOT.Metric

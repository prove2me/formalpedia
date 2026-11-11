-- Prove2me | Theorems.Thm_CorrBoundsPoly_ExactDegree_eq_3_10
-- name    : CorrBoundsPoly.ExactDegree.eq_3_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:58:52.218268+00:00
-- url     : https://prove2.me/theorems/e812a044-cc20-4888-9346-40fd394fbf39
-- title:
--   §3.3, Eq. (3.10) — $\nu(\sigma_{a,3a^2})\le\frac32e^{-3}<\frac1{13}$ for dyadic $a\ge2$
-- statement:
--   For dyadic $a\ge2$, the elementary core $\sigma_{a,3a^2}$ on $3a^2$ variables has normalized rank defect
--   $$\nu(\sigma_{a,3a^2})\le\frac32e^{-3}<\frac1{13}. \tag{3.10}$$
--
--   This is the bound on the dyadic building blocks $E_a=\sigma_{a,3a^2}$ used in the recursion for the exact-degree cores (Lemma 4.3).
--
--   Differences from the source: none.
-- source:
--   Xin Li, More on Correlation Bounds for Polynomials, STOC 2027 submission (manuscript sha256 aa4ef6f7…), p. 29 (PDF 31), §3.3, Eq. (3.10)

import Mathlib
import Definitions.Def_CorrBoundsPoly_ExactDegree_ElemSym

namespace CorrBoundsPoly.ExactDegree

/-- **§3.3, Eq. (3.10)** (Xin Li, *More on Correlation Bounds for Polynomials*, p. 29, PDF 31). For
dyadic `a ≥ 2`, `ν(σ_{a,3a²}) ≤ (3/2) e^{−3} < 1/13`. -/
theorem eq_3_10 (a : ℕ) (ha : IsDyadic a) (ha2 : 2 ≤ a) :
    nu (sigma a (3 * a ^ 2)) ≤ 3 / 2 * Real.exp (-3) ∧ 3 / 2 * Real.exp (-3) < (1 : ℝ) / 13 := by sorry

end CorrBoundsPoly.ExactDegree

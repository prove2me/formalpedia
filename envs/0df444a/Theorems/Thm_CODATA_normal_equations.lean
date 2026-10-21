-- Prove2me | Theorems.Thm_CODATA_normal_equations
-- name    : CODATA.normal_equations
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-21T01:37:07.425985+00:00
-- url     : https://prove2.me/theorems/d8700d90-bae6-46d7-9381-ac858829f688
-- title:
--   The normal equations characterize the minimizers of the chi-square statistic
-- statement:
--   For a weighted least-squares problem whose weight matrix is symmetric
--   and strictly positive definite, a parameter vector minimizes the
--   chi-square statistic of the weighted residuals if and only if it
--   solves the normal equations: every column of the design matrix is
--   orthogonal, relative to the weight matrix, to the residual vector.
--   Moreover, if the design matrix has full column rank, then any two
--   solutions of the normal equations coincide. This is the theorem that
--   makes the CODATA adjustment procedure well defined: the adjusted
--   constants of the 2022 report are determined as the solution of the
--   normal equations, and by this equivalence they are exactly the
--   minimizers of the chi-square statistic, uniquely so at full column
--   rank.
-- source:
--   P. J. Mohr, D. B. Newell, B. N. Taylor and E. Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, J. Phys. Chem. Ref. Data 54, 033105 (2025), doi 10.1063/5.0279860; Rev. Mod. Phys. 97, 025002 (2025), doi 10.1103/RevModPhys.97.025002, section XII: the least-squares adjustment of the 133 input data for the 79 adjusted constants determines the adjusted constants by minimizing the chi-square statistic of the weighted residuals.

import Mathlib
import Definitions.Def_CODATA_lsa
import Definitions.Def_CODATA_uncert
import Definitions.Def_CODATA_values

/-!
# The normal equations characterize the minimizers

Section XII of the 2022 CODATA report describes the determination of
the recommended values as a least-squares adjustment: the adjusted
constants are chosen to minimize the chi-square statistic of the
weighted residuals. This milestone proves the classical equivalence
for the weighted model of `Def_CODATA_lsa`: when the weight matrix is
symmetric and strictly positive definite, the chi-square statistic is
a convex quadratic function of the adjusted constants, so its
minimizers are exactly the solutions of the normal equations; and when
the design matrix has full column rank, the solution of the normal
equations is unique. The milestone is proved on the way to the goal
theorem `CODATA.codata_self_consistent`.
-/

namespace CODATA

/-- For a least-squares problem whose weight matrix is symmetric and
strictly positive definite, the minimizers of the chi-square statistic
are exactly the solutions of the normal equations; and if the design
matrix has full column rank, then any two solutions of the normal
equations coincide. -/
theorem normal_equations {N M : ℕ} (L : LSQ N M) (hG : IsSPD L.G)
    (hA : Function.Injective L.A.mulVec) (x : Fin M → ℝ) :
    (Minimizes L x ↔ SolvesNormal L x) ∧
      ∀ z, SolvesNormal L z → z = x := by
  sorry

end CODATA

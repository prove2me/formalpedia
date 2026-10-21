-- Prove2me | Theorems.Thm_CODATA_weighted_mean
-- name    : CODATA.weighted_mean
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-21T01:37:42.182189+00:00
-- url     : https://prove2.me/theorems/c132d63a-041b-486c-a557-374f67ec61c8
-- title:
--   The single adjusted constant: the weighted mean and its variance
-- statement:
--   For a weighted least-squares problem with one adjusted constant, at
--   least one input datum, zero offsets, observational equations of the
--   form y i = x, and a strictly positive definite weight matrix, the
--   solution x of the normal equations satisfies: x is the weighted mean
--   of the data, the weight being the total sum of the entries of the
--   weight matrix; the one-by-one normal matrix has a two-sided inverse
--   whose single entry, the variance of the adjusted constant, is the
--   reciprocal of the total weight; and every other solution of the
--   normal equations has the same value. This is the situation of the
--   separate adjustment of the sixteen values of the Newtonian constant of
--   gravitation in the 2022 CODATA report: sixteen input data for a single
--   adjusted constant, with the expansion factor 3.9 applied to all the
--   uncertainties.
-- source:
--   P. J. Mohr, D. B. Newell, B. N. Taylor and E. Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, J. Phys. Chem. Ref. Data 54, 033105 (2025), doi 10.1063/5.0279860; Rev. Mod. Phys. 97, 025002 (2025), doi 10.1103/RevModPhys.97.025002, section XII: the separate adjustment of the sixteen values of the Newtonian constant of gravitation for a single adjusted constant, with 16 - 1 = 15 degrees of freedom and expansion factor 3.9.

import Mathlib
import Definitions.Def_CODATA_lsa
import Definitions.Def_CODATA_uncert
import Definitions.Def_CODATA_values

/-!
# The single adjusted constant: the weighted mean

The 2022 CODATA report treats the Newtonian constant of gravitation
separately: an adjustment of sixteen input data for a single adjusted
constant (sixteen minus one equals fifteen degrees of freedom), with
an expansion factor of 3.9 applied to the uncertainties of all the
data. This milestone identifies the general rank-one case of the
least-squares model of `Def_CODATA_lsa`: when every observational
equation reads y i = x + 0, the adjusted constant is the weighted mean
of the data, the weights being the entries of the weight matrix; its
variance is the single entry of the inverse of the normal matrix; and
the adjusted value is unique. This milestone is proved on the way to
the goal theorem `CODATA.codata_self_consistent`.
-/

namespace CODATA

/-- For a least-squares problem with one adjusted constant, at least
one input datum, zero offsets, observational equations y i = x and a
strictly positive definite weight matrix, the adjusted constant at a
solution x of the normal equations is the weighted mean
(sum_i sum_j G i j y j) / (sum_i sum_j G i j); there is a two-sided
inverse C of the normal matrix, the variance of the adjusted constant
is its (0, 0) entry, 1 / (sum_i sum_j G i j); and every other solution
of the normal equations has the same value. -/
theorem weighted_mean {N : ℕ} (L : LSQ N 1) (hN : 0 < N)
    (hG : IsSPD L.G) (hA : ∀ i, L.A i 0 = 1) (hb : ∀ i, L.b i = 0)
    (x : Fin 1 → ℝ) (hx : SolvesNormal L x) :
    x 0 = (∑ i, ∑ j, L.G i j * L.y j) / (∑ i, ∑ j, L.G i j) ∧
      ∃ C, IsCov L C ∧ C 0 0 = 1 / (∑ i, ∑ j, L.G i j) ∧
        ∀ z, SolvesNormal L z → z 0 = x 0 := by
  sorry

end CODATA

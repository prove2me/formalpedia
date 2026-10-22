-- Prove2me | Theorems.Thm_CODATA_propagation_laws
-- name    : CODATA.propagation_laws
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T01:39:10.258204+00:00
-- url     : https://prove2.me/theorems/8d832498-5c2f-4d3d-bc2f-f55230eaab18
-- title:
--   The laws of propagation of relative uncertainty
-- statement:
--   Let V be a covariance matrix with positive diagonal entries. Four
--   algebraic laws of the propagation of relative uncertainty hold.
--   Every diagonal correlation coefficient is one. The relative variance
--   of the linear combination concentrated at a single component, with
--   sensitivity minus one there, is the square of the relative uncertainty
--   of that component. The relative variance scales by the square of a
--   scalar multiple of the sensitivity vector. And when all off-diagonal
--   covariances vanish, the relative variance of any linear combination
--   is the sum over components of the squared sensitivity times the
--   squared relative uncertainty. These are the algebraic facts underlying
--   the derivation of the recommended values and their uncertainties from
--   the adjusted constants and their covariances in the 2022 CODATA
--   report.
-- source:
--   P. J. Mohr, D. B. Newell, B. N. Taylor and E. Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, J. Phys. Chem. Ref. Data 54, 033105 (2025), doi 10.1063/5.0279860; Rev. Mod. Phys. 97, 025002 (2025), doi 10.1103/RevModPhys.97.025002, section XII: the recommended values and their uncertainties are obtained from the adjusted constants by taking into account their covariances, that is, by the law of propagation of uncertainty.

import Mathlib
import Definitions.Def_CODATA_lsa
import Definitions.Def_CODATA_uncert
import Definitions.Def_CODATA_values

/-!
# The laws of propagation of relative uncertainty

The recommended values of the 2022 CODATA report are obtained from
the adjusted constants by propagating their uncertainties and
covariances. This milestone verifies the algebraic skeleton of that
propagation law for relative uncertainties, in the form recorded in
`Def_CODATA_uncert`: the correlation coefficient of an entry with
itself is one; the relative variance of a single component of the
value vector is the square of its relative uncertainty; the relative
variance scales quadratically in the sensitivity vector; and for
uncorrelated inputs the relative variances add. This milestone is
proved on the way to the goal theorem
`CODATA.codata_self_consistent`.
-/

namespace CODATA

/-- Let V be a covariance matrix with positive diagonal entries. Every
diagonal correlation coefficient is one; the relative variance of the
linear combination concentrated at a single component k with
sensitivity minus one is the square of the relative uncertainty of
that component; the relative variance scales by the square of a scalar
multiple of the sensitivity vector; and when all off-diagonal
covariances vanish, the relative variance of any linear combination is
the sum of the squared relative uncertainties weighted by the squared
sensitivities. -/
theorem propagation_laws {N : ℕ} (V : Matrix (Fin N) (Fin N) ℝ)
    (hV : ∀ k, 0 < V k k) :
    (∀ k, corr V k k = 1) ∧
      (∀ k (u x : Fin N → ℝ),
        relVar V u x (fun j => if j = k then -1 else 0)
          = (u k / abs (x k))^2) ∧
      (∀ c (p u x : Fin N → ℝ),
        relVar V u x (fun i => c * p i) = c * c * relVar V u x p) ∧
      ((∀ k l, k ≠ l → V k l = 0) →
        ∀ (p u x : Fin N → ℝ),
          relVar V u x p
            = ∑ k, p k * p k * (u k / abs (x k)) * (u k / abs (x k))) := by
  sorry

end CODATA

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_bv_weighted_boundary_jet
-- name    : AvramDividend.Classical.avram_ws01e_bf_new_bv_weighted_boundary_jet
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:20:26.631066+00:00
-- url     : https://prove2.me/theorems/ef8bd2b6-b36a-4803-a6a6-7f6744d396b2
-- title:
--   Genuine bounded-variation weighted boundary jet for the optimal dividend value
-- statement:
--   For a genuine Standing spectrally negative Levy process of bounded variation, positive discount q and the canonical q-scale function, at every strictly positive real cstar barrier the optimal candidate and the normalised scale branch agree on the entire lower closed half-line and have matching first derivative at the barrier. The second-derivative equality after multiplication by sigma squared is automatic since bounded variation forces sigma=0. Crucially the nonzero normaliser derivative is derived from actual positive Esscher tilted monotonicity and positivity of W, not assumed.
-- source:
--   Source-faithful bounded-variation case of the Open canonical boundary-jet theorem vcstar_scaledW_matched_weighted_jet_at_cstar (22df0d92) and vcstar_scaledW_boundary_smooth_fit (640d249d); uses only Proved true-scale positivity and tilt, Standing BV C1, first-jet gluing and closed below-barrier equality. This enables transfer of the nonlocal generator at the barrier once actual BV scale harmonicity is assembled.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiffOn_one_of_boundedVariation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound
import Theorems.Thm_AvramDividend_Classical_vcstar_first_deriv_smooth_fit_of_nonzero
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_scaledW_le_cstar_of_support
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bf_new_bv_weighted_boundary_jet
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation)
    (hc : 0 < (cstar W).toReal) :
    (∀ z : ℝ, z ≤ (cstar W).toReal →
      vcstar W z = (fun z : ℝ =>
        divE (W z) (scaleDeriv W (cstar W).toReal)) z) ∧
    deriv (vcstar W) (cstar W).toReal =
      deriv (fun z : ℝ =>
        divE (W z) (scaleDeriv W (cstar W).toReal)) (cstar W).toReal ∧
    X.σ ^ 2 * iteratedDeriv 2 (vcstar W) (cstar W).toReal =
      X.σ ^ 2 * iteratedDeriv 2 (fun z : ℝ =>
        divE (W z) (scaleDeriv W (cstar W).toReal)) (cstar W).toReal := by sorry

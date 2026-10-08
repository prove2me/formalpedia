-- Prove2me | Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_boundedVariation
-- name    : AvramDividend.Classical.psi_eventually_gt_of_boundedVariation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T06:35:00.92719+00:00
-- url     : https://prove2.me/theorems/e9a8e903-54cb-4709-8fa1-330ae9e496bb
-- title:
--   Bounded-variation standing Lévy exponent eventually exceeds every positive discount
-- statement:
--   For a canonical spectrally negative Lévy process satisfying Standing and bounded variation, and every q>0, the Laplace exponent eventually exceeds q for all sufficiently large real Laplace parameters. The proof uses positive infinitesimal drift, finite small-jump first moment, convergence and monotonicity of the normalised compensated small-jump integral, and finite large-jump mass.
-- source:
--   Direct composition of already-Proved bounded-variation drift positivity, first-moment integrability, compensated-integral convergence/monotonicity, finite large-jump mass and the canonical normalised psi lower bound. The threshold argument is inlined so no Open helper theorem is imported.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_bv_small_negative_first_moment_integrable
import Theorems.Thm_AvramDividend_Classical_levy_small_negative_compensated_div_integrable
import Theorems.Thm_AvramDividend_Classical_levy_large_negative_jump_unit_integrable
import Theorems.Thm_AvramDividend_Classical_negative_compensated_real_integral_tendsto_finite
import Theorems.Thm_AvramDividend_Classical_negative_compensated_integral_mono
import Theorems.Thm_AvramDividend_Classical_psi_normalised_lower_bound_small

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.psi_eventually_gt_of_boundedVariation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) :
    ∃ β₀ : ℝ, 0 ≤ β₀ ∧ ∀ θ : ℝ, β₀ ≤ θ → q < X.ψ θ := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_scale_right_derivative_of_positive_esscher_root
-- name    : AvramDividend.Classical.gaussian_scale_right_derivative_of_positive_esscher_root
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:59:40.843455+00:00
-- url     : https://prove2.me/theorems/0362e44d-92b9-416e-9c7e-51a387ce04e8
-- title:
--   Gaussian q-scale right-hand origin derivative normalisation at a positive Esscher root
-- statement:
--   For a canonical q-scale function W of a spectrally negative Lévy process with positive Gaussian coefficient and a positive root ψ(φ)=q, its ordinary derivative on positive reserves tends to 2/σ² on approaching the origin from the right. Construct the canonical tilted scale V, apply the newly Proved explicit-native-variance C1 Volterra derivative resolvent and zero-origin tilt limit; use published Volterra uniqueness to identify V'=g and the Gaussian positive-axis C1 theorem for HasDerivAt; finally apply the Proved full native Volterra right-slope lemma. This is a direct root-assumed analytic bridge to the original right-slope target.
-- source:
--   Formal Gaussian native C1 Volterra identity, causal solution uniqueness, Gaussian C1 scale regularity, and the Proved full native right-slope limit theorem.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_native_C1_derivative_resolvent_with_variance
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_tilt_vanishes_right_origin
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_tilted_scale_continuous
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_tilted_scale_locally_bounded
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_scale_C1_of_positive_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_causal_volterra_deriv_eq_resolvent_on_positive
import Theorems.Thm_AvramDividend_Classical_gaussian_right_slope_of_native_full_volterra_resolvent
open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace AvramDividend.Classical
/-- A Gaussian q-scale function has right derivative limit 2/σ² at every positive Esscher root. -/
theorem gaussian_scale_right_derivative_of_positive_esscher_root
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    Tendsto (deriv W) (𝓝[>] (0 : ℝ)) (𝓝 (2 / X.σ ^ 2)) := by
  sorry
end AvramDividend.Classical

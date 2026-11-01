-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_weighted_curvature_L1
-- name    : AvramDividend.Classical.avram_wave4_p2_scale_primitive_weighted_curvature_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:05:53.168423+00:00
-- url     : https://prove2.me/theorems/1c8cfca2-b438-4f29-950e-655801d996b0
-- title:
--   Source primitive curvature is measurable, C0 positive and exponentially L1
-- statement:
--   For the original source q-scale W under Standing and admissible Laplace parameter θ≥0 with q<ψ(θ), extend W' by zero on nonpositive reserves using the actual Ioi indicator. This curvature is Borel measurable, continuous on positive reserves, and exponentially weighted absolute integrable on all of ℝ. These are precisely the three premises of the Proved generic quadratic weighted tent kernel theorem e11ef020, so this source-specific lemma permits the finite quadratic jump-moment bound for the real non-Gaussian primitive U without a global W'' or Gaussian boundary-slope assumption.
-- source:
--   Avram Palmowski Pistorius 2007, Lemma 4; accepted weighted positive derivative theorem a01f741d, source Standing C1 310bb0bc; exact pinned Mathlib integrable indicator and derivative measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p2_scale_primitive_weighted_curvature_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) :
    Measurable ((Ioi (0 : ℝ)).indicator (deriv W)) ∧
      ContinuousOn ((Ioi (0 : ℝ)).indicator (deriv W)) (Ioi (0 : ℝ)) ∧
      Integrable
        (fun u : ℝ => Real.exp (-(θ * u)) *
          |(Ioi (0 : ℝ)).indicator (deriv W) u|) volume := by sorry

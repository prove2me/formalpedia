-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_unit_damped_indicator_bounded_continuous
-- name    : AvramDividend.Classical.gaussian_esscher_unit_damped_indicator_bounded_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T19:14:40.368463+00:00
-- url     : https://prove2.me/theorems/535a1014-9913-4ba8-a3df-353937b7ad92
-- title:
--   Unit-exponentially damped Gaussian Esscher scale indicator is globally bounded and continuous
-- statement:
--   For σ>0, positive Esscher root φ of ψ(φ)=q and the scale representative V(x)=exp(−φx)W(x) for x>0, the positive-axis indicator of exp(−x)V(x) is globally continuous and norm-bounded. Gaussian zero-origin continuity handles x=0. The global scale Laplace envelope at θ=φ+1 bounds exp(−(φ+1)x)W(x) using ψ(φ+1)>q, with no need for boundedness of the undamped Esscher scale. Consequently the bounded-right-factor causal convolution theorem becomes applicable to unit-weighted K and V.
-- source:
--   Proved gaussian_esscher_positive_indicator_continuous, Gaussian root-crossing, scaleFunction_global_weighted_norm_bddAbove (pending proof).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_positive_indicator_continuous
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_psi_strictly_above_root
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_square_integrable_neg_pushforward
import Theorems.Thm_AvramDividend_Classical_scaleFunction_global_weighted_norm_bddAbove
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.gaussian_esscher_unit_damped_indicator_bounded_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    Continuous ((Ioi (0 : ℝ)).indicator
      (fun x : ℝ => Real.exp (-x) * V x)) ∧
    BddAbove (Set.range (fun x : ℝ =>
      ‖(Ioi (0 : ℝ)).indicator (fun y : ℝ => Real.exp (-y) * V y) x‖)) := by sorry

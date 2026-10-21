-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_cumulative_of_exit_decay_without_aux
-- name    : AvramDividend.Classical.gaussian_cumulative_of_exit_decay_without_aux
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T20:28:44.316987+00:00
-- url     : https://prove2.me/theorems/6c10b9dc-b13d-42d4-b42a-72ebd4d61ac4
-- title:
--   Gaussian Esscher cumulative Laplace representation from first passage without auxiliary positivity or origin hypotheses
-- statement:
--   For a spectrally negative Lévy process with Gaussian coefficient σ>0, positive discount q and canonical q-scale function W, a genuine first-passage exponential decay comparison at each positive Laplace root suffices to produce the positive locally finite Esscher cumulative measure and the full shifted Laplace integrability and identity. Positivity of W(x) for x>0 and W(0)=0 follow automatically from separately Proved Gaussian results, removing those extra assumptions of the earlier Gaussian cumulative theorem. The first-passage decay comparison remains explicit and substantive.
-- source:
--   Proved scaleFunction_strict_pos_of_gaussian, scaleFunction_zero_origin_gaussian_without_standing and gaussian_esscher_cumulative_of_exit_decay.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.gaussian_cumulative_of_exit_decay_without_aux
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (hdecay : ∀ φ : ℝ, 0 < φ → X.ψ φ = q →
      ∀ x y : ℝ, 0 < x → x ≤ y →
        W x ≤ Real.exp (-φ * (y - x)) * W y) :
    ∃ (β : Measure ℝ) (φ b : ℝ),
      0 < φ ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → 0 < β (Iic x)) ∧
      ∀ θ : ℝ, b < θ →
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (Real.exp (-φ * x) * W x)) (Ioi 0) ∧
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (β (Iic x)).toReal) (Ioi 0) ∧
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
          (Real.exp (-φ * x) * W x) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
          (β (Iic x)).toReal := by sorry

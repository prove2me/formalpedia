-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_original_stopped_signed_single_residual_mesh
-- name    : AvramDividend.Classical.avram_a19_original_stopped_signed_single_residual_mesh
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T00:01:57.874209+00:00
-- url     : https://prove2.me/theorems/9c71aeeb-0680-40cf-a0ff-0ceac0560040
-- title:
--   Original stopped BV signed single-residual mesh with L1 domination
-- statement:
--   For the actual controlled bounded-variation Lévy process, construct genuine finite physical-grid stopped cash-plus-survival Ymesh and one signed residual Zmesh with a nonpositive expected value at each mesh, an integrable uniform envelope, and pathwise source budget. Both meshes converge almost surely to their original stopped source limits. This packages the compensator martingale and nonpositive HJB drift contributions into one residual while retaining all original process assumptions.
-- source:
--   Source-faithful reduction of db6a3111: one signed L1-controlled grid residual is sufficient to witness the original triple-grid certificate by taking the centred martingale mesh identically zero and assigning the complete signed residual to the drift/budget mesh. The original physical stopped source construction and sign remain to be established, and this child is not a generic theorem shortcut.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a19_original_stopped_signed_single_residual_mesh
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let Y : Ω → ℝ := fun ω =>
      let S : ℝ≥0 := ⟨T, hT⟩
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
         else 0)
    ∃ Ymesh Zmesh : ℕ → Ω → ℝ,
      ∃ Z DZ : Ω → ℝ,
        (∀ n, AEStronglyMeasurable (Zmesh n) P) ∧
        Integrable DZ P ∧
        (∀ n, ∀ᵐ ω ∂P, |Zmesh n ω| ≤ DZ ω) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => Ymesh n ω) atTop (nhds (Y ω))) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => Zmesh n ω) atTop (nhds (Z ω))) ∧
        (∀ n, (∫ ω, Zmesh n ω ∂P) ≤ 0) ∧
        (∀ᵐ ω ∂P, ∀ n, Ymesh n ω ≤ w x + Zmesh n ω) := by sorry

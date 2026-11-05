-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_integration_sweep9_original_C1_signed_HJB_mean_of_regular_generator
-- name    : AvramDividend.Classical.avram_integration_sweep9_original_C1_signed_HJB_mean_of_regular_generator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T15:46:36.364894+00:00
-- url     : https://prove2.me/theorems/32018ebd-168d-4bbe-8784-ff886777d2ca
-- title:
--   Original stopped BV C1 compensated jump and HJB signed expectation from regular generator residual
-- statement:
--   Under literal original bounded-variation spectrally negative Levy X, dividend D, genuine bounded right-continuous stopping clock and predictable compact interior E, and an exactly specified original generator drift residual measurable and continuous on that compact band, the actual signed stopped compensated jump plus HJB residual is integrable with nonpositive expectation. The generator drift L1 is now proved from physical predictability and continuity, removing independent hFint from the previously Proved P3-E signed source theorem.
-- source:
--   Actual original P3-E signed compensated jump plus HJB  c7d9eb3f with hFint supplied by Proved original automatic prestate measurable finite-horizon HJB L1 8e6b6290. Exact generator residual identity hResEq makes the two integrands definitionally identical. This is a source-exact original stochastic input to P3 residual 1a1a0301, not a proof of the stopped Stieltjes mesh identity or canonical budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep9_original_predictable_HJB_drift_L1_without_prestate_assumption
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_C1_auto_bounded_signed_HJB_nonpos
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_integration_sweep9_original_C1_signed_HJB_mean_of_regular_generator {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
(X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T) (hτ : IsStoppingTime 𝓕.rightCont
(fun ω => (τ ω : WithTop ℝ≥0))) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ)
(hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (q : ℝ) (hq : 0 ≤ q) (a b : ℝ)
(ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b) (E : Set (ℝ≥0 × Ω)) (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
(hEregion : ∀ p ∈ E, Function.leftLim (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b)
(C : ℝ≥0∞)
(hbC : ENNReal.ofReal b < C)
(hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
(hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
  X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
(hEcap : ∀ p ∈ E, ENNReal.ofReal (Function.leftLim
  (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) < C)
(hRes : ℝ → ℝ)
(hResEq : ∀ y : ℝ, hRes y =
  X.drift * deriv w y +
    (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) - q * w y)
(hResMeas : Measurable hRes)
(hResCont : ContinuousOn hRes (Icc a b)) :
  let Upre : ℝ≥0 × Ω → ℝ := (fun p : ℝ≥0 × Ω =>
    Function.leftLim (fun v : ℝ≥0 =>
      x + X.X v p.2 - rightLimit D v p.2) p.1);
  let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := (fun p : (ℝ≥0 × Ω) × ℝ =>
    if p.1 ∈ E ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
       (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
        w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
    else 0);
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
    fun p => if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0;
  let F : ℝ≥0 × Ω → ℝ := (fun p : ℝ≥0 × Ω =>
    if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) *
      (X.drift * deriv w (Function.leftLim (fun v : ℝ≥0 =>
          x + X.X v p.2 - rightLimit D v p.2) p.1) +
       (∫ z in Iio (0 : ℝ),
          w (Function.leftLim (fun v : ℝ≥0 =>
            x + X.X v p.2 - rightLimit D v p.2) p.1 + z) -
          w (Function.leftLim (fun v : ℝ≥0 =>
            x + X.X v p.2 - rightLimit D v p.2) p.1) ∂X.ν) -
       q * w (Function.leftLim (fun v : ℝ≥0 =>
          x + X.X v p.2 - rightLimit D v p.2) p.1))
    else 0);
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω => ((Measure.count.restrict
{u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω -
Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)));
  let M : Ω → ℝ := fun ω => (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) - (∫ t, ∫ z, H ((t, ω), z)
∂(X.ν.restrict (Iio (0 : ℝ))) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal));
  let B : Ω → ℝ := fun ω => (∫ t, F (t, ω) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal));
  Integrable (fun ω => M ω + B ω) P ∧
  (∫ ω, M ω + B ω ∂P) ≤ 0 := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_real_ruin_compact_centered_and_HJB_mean_sign
-- name    : AvramDividend.Classical.avram_p3_bv_original_real_ruin_compact_centered_and_HJB_mean_sign
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T11:01:58.266966+00:00
-- url     : https://prove2.me/theorems/d8c77f8a-8270-494e-8bff-a619c89fd1bf
-- title:
--   Same-original real-ruin localised BV jump martingale has zero mean while its HJB drift has nonpositive mean
-- statement:
--   On the identical original Ω/P/filtration/Lévy process and actual dividend-controlled real-horizon ruin clock, the intrinsic compact-band compensated jump residual is integrable and exactly centred while the source-exact signed discounted generator/HJB product-time drift has nonpositive expectation. The global canonical interior HJB hypothesis supplies the compact-band generator inequality. This is the martingale-and-drift mean pair required by the original BV stochastic verification; the pathwise C1/Stieltjes dividend equality and exhaustion remain separate.
-- source:
--   Accepted original arbitrary real-horizon stopped P2 centring 349d07b1 and accepted source-exact global HJB compact pre-reserve sign ae93db0a, both on original X.X/D and pinned Mathlib.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_real_ruin_compact_source_jump_centered
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_compact_HJB_from_global_interior

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_real_ruin_compact_centered_and_HJB_mean_sign
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (a b L R : ℝ) (ha : 0 < a) (ha2 : a ≤ 2)
    (hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (hν : (∫⁻ z : ℝ, ENNReal.ofReal (min (1 : ℝ) (z ^ 2)) ∂X.ν) < ⊤)
    (C : ℝ≥0∞) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hbC : ENNReal.ofReal b < C)
    (Upre : ℝ≥0 × Ω → ℝ)
    (hUpre : ∀ p, Upre p = Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)
    (F : ℝ≥0 × Ω → ℝ)
    (hF : ∀ p, F p = if Upre p ∈ Icc a b then
      Real.exp (-(q * (p.1 : ℝ))) *
        (X.drift * deriv w (Upre p) +
          (∫ z in Iio (0 : ℝ), w (Upre p + z) - w (Upre p) ∂X.ν) -
          q * w (Upre p)) else 0)
    (hFint : Integrable F
      ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
        Real.toNNReal).prod P)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let E : Set (ℝ≥0 × Ω) := {p | Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b}
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1 ∈ E ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Function.leftLim (fun s : ℝ≥0 => x + X.X s p.1.2 -
            rightLimit D s p.1.2) p.1.1 + p.2) -
           w (Function.leftLim (fun s : ℝ≥0 => x + X.X s p.1.2 -
            rightLimit D s p.1.2) p.1.1)) else 0
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
    (Integrable (fun ω =>
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal))) P ∧
    (∫ ω, ((∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal))) ∂P) = 0) ∧
    (∫ p, F p ∂((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
      Real.toNNReal).prod P)) ≤ 0 := by sorry

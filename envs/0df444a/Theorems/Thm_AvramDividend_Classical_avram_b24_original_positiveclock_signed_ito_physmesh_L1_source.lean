-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_positiveclock_signed_ito_physmesh_L1_source
-- name    : AvramDividend.Classical.avram_b24_original_positiveclock_signed_ito_physmesh_L1_source
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T13:37:50.595299+00:00
-- url     : https://prove2.me/theorems/8f7bd137-0458-47b1-b0b8-110844bb52ca
-- title:
--   Strictly positive ruin-clipped clock original signed Ito meshes with nonnegative vanishing L1 error
-- statement:
--   Build actual original same-source bounded predictable Gaussian and compensated negative-mark stopped physical C2 Ito-Meyer meshes and a nonnegative integrable L1-vanishing signed error, with both gain sequences L1-Cauchy. The discounted HJB and full inclusive Iic Stieltjes cash plus terminal reserve pathwise inequality is required on every strictly positive ruin-clipped stopping-clock path. The time-zero branch is separately proved including initial right payment, and finite mesh source gains vanish there. The independent reduction combines both cases for the full original sigma without any post-ruin continuation.
-- source:
--   Avram-Palmowski-Pistorius (2007) Proposition 4(i), (5.13) genuine ruin-stopped Ito-Meyer and finite-variation contact budget, combined with Protter stopped compensation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_positiveclock_signed_ito_physmesh_L1_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (hσclip : ∀ ω, σ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
       Tendsto (fun k : ℕ =>
         avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
         atTop (𝓝 (R u ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
       Tendsto (fun k : ℕ =>
         avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
         atTop (𝓝 (Jsmall u ω))) :
    ∃ (G J E : ℕ → Ω → ℝ),
      (∀ m, Integrable (E m) P) ∧
      (∀ m, ∃ (S : Finset ℕ) (a b : ℕ → ℝ≥0)
        (WG WJ : ℕ → Ω → ℝ) (LG LJ : ℝ),
        (∀ i ∈ S, a i ≤ b i) ∧
        (∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WG i)) ∧
        (∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WJ i)) ∧
        0 ≤ LG ∧ 0 ≤ LJ ∧
        (∀ i ∈ S, ∀ ω, ‖WG i ω‖ ≤ LG) ∧
        (∀ i ∈ S, ∀ ω, ‖WJ i ω‖ ≤ LJ) ∧
        (∀ ω, G m ω =
          ∑ i ∈ S, (if σ ω ≤ a i then 0 else WG i ω) *
            (R (b i) ω - R (a i) ω)) ∧
        (∀ ω, J m ω =
          ∑ i ∈ S, (if σ ω ≤ a i then 0 else WJ i ω) *
            (Jsmall (b i) ω - Jsmall (a i) ω))) ∧
      (∀ m, ∀ᵐ ω ∂P, 0 < σ ω →
        F ω ≤ w x + G m ω + J m ω + E m ω) ∧
      (∀ m, ∀ᵐ ω ∂P, 0 ≤ E m ω) ∧
      (∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ m l : ℕ, N ≤ m → N ≤ l →
          (∫ ω, ‖G m ω - G l ω‖ ∂P) ≤ ε) ∧
      (∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ m l : ℕ, N ≤ m → N ≤ l →
          (∫ ω, ‖J m ω - J l ω‖ ∂P) ≤ ε) ∧
      (∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
          (∫ ω, ‖E m ω‖ ∂P) ≤ ε) := by sorry

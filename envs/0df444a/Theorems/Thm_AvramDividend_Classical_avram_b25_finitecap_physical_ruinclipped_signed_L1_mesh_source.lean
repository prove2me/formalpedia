-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b25_finitecap_physical_ruinclipped_signed_L1_mesh_source
-- name    : AvramDividend.Classical.avram_b25_finitecap_physical_ruinclipped_signed_L1_mesh_source
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T00:58:46.450857+00:00
-- url     : https://prove2.me/theorems/5c8f13e8-def9-407e-bd84-4dcab0bf8ff8
-- title:
--   Original finite-cap ruin-clipped physical Ito-Meyer mesh: signed cash and genuine two-noise L1 Cauchy source
-- statement:
--   For the original finite-cap nonzero-Gaussian finite-negative-jump-activity Levy dividend model, produce adapted bounded predictable physical stopped mesh Gaussian and compensated jump gains and integrable signed Ito-Meyer errors with exact physical ruin-clipped terminal and inclusive Iic/right-dividend cash. Show positive-clock cash domination by the two gains plus signed error and gain L1 Cauchy/error L1 vanishing. This is strictly weaker than the parent, separating stochastic Ito work from abstract subsequence/envelope extraction. Cap-contact linear-extension terms and the terminal ruin cell must be accounted for.
-- source:
--   Source-faithful decomposition of B25 finitecap bbacb9a7 from Protter (2005) II.7 Theorem 32; uses actual clock/cash and does not presume post-ruin or original target.

import Mathlib
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_b25_finitecap_physical_ruinclipped_signed_L1_mesh_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hCapFinite : C ≠ ⊤)
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
      (∀ k, Integrable (G k) P) ∧
      (∀ k, Integrable (J k) P) ∧
      (∀ k, Integrable (E k) P) ∧
      (∀ k, ∃ (S : Finset ℕ) (a b : ℕ → ℝ≥0)
        (WG WJ : ℕ → Ω → ℝ) (LG LJ : ℝ),
        (∀ i ∈ S, a i ≤ b i) ∧
        (∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WG i)) ∧
        (∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WJ i)) ∧
        0 ≤ LG ∧ 0 ≤ LJ ∧
        (∀ i ∈ S, ∀ ω, ‖WG i ω‖ ≤ LG) ∧
        (∀ i ∈ S, ∀ ω, ‖WJ i ω‖ ≤ LJ) ∧
        (∀ ω, G k ω =
          ∑ i ∈ S, (if σ ω ≤ a i then 0 else WG i ω) *
            (R (b i) ω - R (a i) ω)) ∧
        (∀ ω, J k ω =
          ∑ i ∈ S, (if σ ω ≤ a i then 0 else WJ i ω) *
            (Jsmall (b i) ω - Jsmall (a i) ω))) ∧
      (∀ k, ∀ᵐ ω ∂P,
        0 < σ ω → F ω ≤ w x + G k ω + J k ω + E k ω) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m l : ℕ,
        N ≤ m → N ≤ l → (∫ ω, ‖G m ω - G l ω‖ ∂P) ≤ ε) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m l : ℕ,
        N ≤ m → N ≤ l → (∫ ω, ‖J m ω - J l ω‖ ∂P) ≤ ε) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m : ℕ,
        N ≤ m → (∫ ω, ‖E m ω‖ ∂P) ≤ ε) := by sorry

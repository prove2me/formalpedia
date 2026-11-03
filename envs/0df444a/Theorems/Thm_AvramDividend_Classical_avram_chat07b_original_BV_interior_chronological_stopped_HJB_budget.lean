-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat07b_original_BV_interior_chronological_stopped_HJB_budget
-- name    : AvramDividend.Classical.avram_chat07b_original_BV_interior_chronological_stopped_HJB_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:56:09.639209+00:00
-- url     : https://prove2.me/theorems/14ba789d-07f7-46f4-87ee-5b61956aef84
-- title:
--   Actual BV C¹ interior reserve localisation and chronological stopped source imply the full expected HJB Stieltjes budget
-- statement:
--   For the actual original bounded-variation spectrally negative Levy source, cap-admissible dividends, stopping time and min-clipped grids, suppose the literal pre/post-payment reserves lie almost surely in a positive compact strip within the HJB interior. BV C1 smoothness then provides the exact local Lipschitz constant required by the accepted cofinal chronological timing theorem. Together with the separately explicit original source subsequence convergence, real M/G/H integrability and chronological Stieltjes residual bound, the accepted source budget yields real expected terminal/cash inequalities and the exact ENNReal outer lintegral dividend bound. This does not assume the payout conclusion, nor claim positive interior localisation at ruin.
-- source:
--   Avram, Palmowski, Pistorius Proposition 4(i); genuine original BV C1 finite-variation local reserve band and source-grid expected HJB bridge; exact Proved inputs 01748a98 and 5fe7a4aa.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_actual_bv_ae_clipped_stopped_grid_local_lipschitz_from_interior_band
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_chronological_stieltjes_hjb_budget_from_cofinal_source
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_chat07b_original_BV_interior_chronological_stopped_HJB_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : (¬ X.BoundedVariation → ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (T : ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτruin : ∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → ℕ)
    (hmono : ∀ n, Monotone (u n)) (hzero : ∀ n, u n 0 = 0)
    (hcover : ∀ ω, ∀ᶠ n in atTop, τ ω ≤ u n (k n))
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
    (W Cash Term M G H : Ω → ℝ)
    (Source Dividend PaymentResidual : ℕ → Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
        (hSource : ∀ n ω, Source n ω =
      let v : ℕ → ℝ≥0 := fun i => min (u n i) (τ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      ∑ i ∈ Finset.range (k n),
        ((E (v (i + 1)) - E (v i)) * w (Y (v i)) +
          E (v (i + 1)) * (w (Z i) - w (Y (v i)))))
    (hDividend : ∀ n ω, Dividend n ω =
      let v : ℕ → ℝ≥0 := fun i => min (u n i) (τ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      let pre : Prop := τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      (w (x - rightLimit D 0 ω) - w x) +
        (∑ i ∈ Finset.range (k n),
          ((E (v (i + 1)) - E (v i)) * w (Y (v i)) +
            E (v (i + 1)) * (w (Z i) - w (Y (v i))) +
            E (v (i + 1)) *
              (w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) +
            E (v (i + 1)) *
              (w (Y (v (i + 1))) -
                w (riskProcess X x D (v (i + 1)) ω)))) +
        (if pre then 0 else E (τ ω) *
          (w (riskProcess X x D (τ ω) ω) - w (Y (τ ω)))) -
        Source n ω)
    (hPaymentResidual : ∀ n ω, PaymentResidual n ω =
      let v : ℕ → ℝ≥0 := fun i => min (u n i) (τ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      let pre : Prop := τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      (w (x - rightLimit D 0 ω) - w x) +
        (∑ i ∈ Finset.range (k n), E (v (i + 1)) *
          (w (Y (v (i + 1))) - w (Z i))) +
        (if pre then 0 else E (τ ω) *
          (w (riskProcess X x D (τ ω) ω) - w (Y (τ ω)))))
    (hSourceSubsequence : ∀ᵐ ω ∂P, Tendsto (fun n => Source (φ n) ω) atTop (𝓝 (M ω + G ω)))
    (m : ℕ → ℝ) (hm : ∀ n, 0 ≤ m n)
    (hmesh : ∀ n i, i < k n →
      ((u n (i + 1) : ℝ) - (u n i : ℝ)) ≤ m n)
    (hmesh0 : Tendsto m atTop (𝓝 0))
    (Timing : ℕ → Ω → ℝ)
    (hTiming : ∀ n ω, Timing n ω =
      (let v : ℕ → ℝ≥0 := fun i => min (u (φ n) i) (τ ω)
       ∑ i ∈ Finset.range (k (φ n)),
         (Real.exp (-(q * (v i : ℝ))) -
           Real.exp (-(q * (v (i + 1) : ℝ)))) *
           |w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
             w (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω)|))
    (cap : ℝ)
    (hCapInterior : Ioo 0 cap ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hInterior : ∀ᵐ ω ∂P, ∃ a b : ℝ,
      a < b ∧ Icc a b ⊆ Ioo 0 cap ∧
      (∀ n i, i < k n →
        x + X.X (min (u n (i + 1)) (τ ω)) ω -
          rightLimit D (min (u n i) (τ ω)) ω ∈ Icc a b) ∧
      (∀ n i, i < k n →
        x + X.X (min (u n (i + 1)) (τ ω)) ω -
          rightLimit D (min (u n (i + 1)) (τ ω)) ω ∈ Icc a b))
    (hChronological : ∀ᵐ ω ∂P, ∀ n,
      PaymentResidual (φ n) ω + Cash ω ≤ H ω + Timing n ω)
    (hMI : Integrable M P) (hGI : Integrable G P) (hHI : Integrable H P)
    (hMzero : (∫ ω, M ω ∂P) = 0) (hGHmean : (∫ ω, G ω + H ω ∂P) ≤ 0) :
    Integrable Cash P ∧ (∫ ω, Term ω + Cash ω ∂P) ≤ w x ∧
    (∫ ω, Cash ω ∂P) ≤ w x ∧
    (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by sorry

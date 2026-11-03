-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_book_terminal_subsequence_hjb_expected_dividend_budget_no_atom
-- name    : AvramDividend.Classical.avram_wave6_06_original_book_terminal_subsequence_hjb_expected_dividend_budget_no_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:41:05.906484+00:00
-- url     : https://prove2.me/theorems/ddd1f584-aef2-44fd-b8fe-bcf024ddf0ba
-- title:
--   Literal book Uτ expected dividend budget from cofinal source HJB and terminal no-atom condition
-- statement:
--   The exact original spectrally negative Levy X, capped admissible dividend strategy D and bounded right-continuous ruin-stopped tau satisfy the literal book U_tau terminal-plus-complete-inclusive-dividend expected bound under Proposition 4(i) local source HJB BV C1/UBV C2, w(0)>=0, the common cofinal physical source/Stieltjes limit, centered integrable physical M and nonpositive expected total drift, and the necessary explicit terminal no-right-dividend-atom equation D_(tau+)=D_tau. This imports the Proved cofinal expected-budget theorem and original piecewise/book endpoint bridge. It does not assert the missing stochastic chain rule.
-- source:
--   Avram Proposition 4(i), Eq. (5.13), original left-continuous D and book riskProcess endpoint; Proved 240892a0 and da64f8a5.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_source_subsequence_asymptotic_hjb_expected_budget_mean_drift
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_no_terminal_payment_atom_expected_book_budget_from_source_piecewise
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_original_book_terminal_subsequence_hjb_expected_dividend_budget_no_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 < q)
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
    (Source Dividend : ℕ → Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω else riskProcess X x D (τ ω) ω)
    (hNoAtom : ∀ ω, rightLimit D (τ ω) ω = D (τ ω) ω)
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
    (hSourceSubsequence : ∀ᵐ ω ∂P, Tendsto (fun n => Source (φ n) ω) atTop (𝓝 (M ω + G ω)))
    (hDividendApproxSubsequence : ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, Dividend (φ n) ω + Cash ω ≤ H ω + ε)
    (hMI : Integrable M P) (hGI : Integrable G P) (hHI : Integrable H P)
    (hMzero : (∫ ω, M ω ∂P) = 0) (hGHmean : (∫ ω, G ω + H ω ∂P) ≤ 0) :
    (∫ ω, Real.exp (-(q * (τ ω : ℝ))) * w (riskProcess X x D (τ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ∂P) ≤ w x := by sorry

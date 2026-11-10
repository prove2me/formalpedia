-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gtop20_original_lower_exit_cofinal_floor_clocks
-- name    : AvramDividend.Classical.avram_gtop20_original_lower_exit_cofinal_floor_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T01:33:57.814549+00:00
-- url     : https://prove2.me/theorems/f9caff29-b479-4941-96ab-b0c6602378af
-- title:
--   Original Gaussian sampled lower reserve exits exhaust stopped horizon
-- statement:
--   Necessary child of the original zero-jump Gaussian physical compact-clock construction: build genuine monotone right-continuous stopping clocks, bounded by the physical stopped horizon, almost surely cofinal even at ruin, with a positive prepayment reserve floor on every strict prefix. Use proven lower exit and stopped-regularity facts, handling time zero and the ruin contact.
-- source:
--   Exact lower-floor and almost-sure cofinality subproblem of existing root-connected Open 22bf1d41. Proved e129ae1d, 9fcc99ab, 0e9f7014, 79fe7676 geometric inputs.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gtop20_original_lower_exit_cofinal_floor_clocks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
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
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσle : ∀ ω, σ ω ≤ τ ω) :
    ∃ L : ℕ → Ω → ℝ≥0,
      (∀ j, IsStoppingTime 𝓕.rightCont (fun ω => (L j ω : WithTop ℝ≥0))) ∧
      (∀ j ω, L j ω ≤ σ ω) ∧
      (∀ ω, Monotone (fun j : ℕ => L j ω)) ∧
      (∀ᵐ ω ∂P, Tendsto (fun j => L j ω) atTop (nhds (σ ω))) ∧
      (∀ j, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < L j ω →
        (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω) := by sorry

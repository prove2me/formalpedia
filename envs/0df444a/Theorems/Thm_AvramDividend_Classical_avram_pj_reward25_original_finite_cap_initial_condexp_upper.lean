-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward25_original_finite_cap_initial_condexp_upper
-- name    : AvramDividend.Classical.avram_pj_reward25_original_finite_cap_initial_condexp_upper
-- status  : Open
-- author  : @WillR
-- created : 2026-11-09T22:12:04.654508+00:00
-- url     : https://prove2.me/theorems/05ac0c40-3d83-4a66-879c-e89e129e7dd0
-- title:
--   Original pure-jump finite-cap physical stopped reward has initial-filtration conditional upper bound
-- statement:
--   For precisely the original pure-jump controlled Lévy process, finite cap and physical bounded stop ρ≤min(ruin,n), assuming integrability of exact zero-normalised terminal plus inclusive dividend cash G, prove condExp_{F.rightCont 0}(G)≤w(x) almost surely. This is the remaining stochastic stopped Itô–Meyer/source budget. It implies the existing conditional-centred majorant d8cdab80 through Proved c80460e8, separating martingale witness extraction from the genuine physical source inequality. No arbitrary-grid or near-zero domination is assumed.
-- source:
--   Exact source-preserving child of d8cdab80. The parent can be constructed from c80460e8 using letI : IsProbabilityMeasure P := X.isProbability. The child is a conditional expected upper bound at the original physical clock and must be proved by stopped Itô–Meyer, weighted marked jumps, HJB sign, and exact dividend/ruin/horizon ledger.

import Mathlib
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward25_original_finite_cap_initial_condexp_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaZero : X.σ = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hCfinite : C ≠ ⊤)
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
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) :
    let G : Ω → ℝ := fun ω =>
      if ρ ω = 0 then w x else
        Real.exp (-(q * (ρ ω : ℝ))) *
          w (if (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
              x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
            else riskProcess X x D (ρ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
    Integrable G P →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P G ω ≤ w x := by sorry

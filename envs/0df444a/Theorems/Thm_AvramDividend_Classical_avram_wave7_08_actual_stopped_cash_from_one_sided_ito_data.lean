-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_actual_stopped_cash_from_one_sided_ito_data
-- name    : AvramDividend.Classical.avram_wave7_08_actual_stopped_cash_from_one_sided_ito_data
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:36:36.755235+00:00
-- url     : https://prove2.me/theorems/eec2510a-df00-4c0f-9c69-e07354f6d8d0
-- title:
--   Canonical UBV source stopped Cash bound from explicit one-sided Ito and centred martingale data
-- statement:
--   For the genuine unbounded-variation original Lévy process, x>0, corrected w(0)>=0, exact source HJB and admissible D, and the actual finite ruin-truncated stopping clock τ, an explicitly assumed stopped one-sided controlled Ito inequality with centered integrable martingale and nonpositive integrable drift yields the exact expected original Stieltjes Cash bound. Automatic clock bounds are derived from Proved 6b7a13a0. The source W6-06 theorem 8cd5e123 gives the complete ENNReal expected cash inequality; no new probabilistic fact or replacement process is assumed.
-- source:
--   Genuine original-process conditional adapter: imports only Proved 6b7a13a0 and Proved 8cd5e123; isolates the remaining IsStoppingTime, strong measurability, martingale centring, drift sign, and Ito upper bound obligations for W7-05/06/07/08.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_actual_stopped_cash_from_one_sided_ito_data
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτEq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτStop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term M G H : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashMeas : AEStronglyMeasurable Cash P)
    (hMI : Integrable M P) (hGI : Integrable G P) (hHI : Integrable H P)
    (hMzero : (∫ ω, M ω ∂P) = 0)
    (hGHnonpos : ∀ᵐ ω ∂P, G ω + H ω ≤ 0)
    (hUpper : ∀ᵐ ω ∂P,
      Term ω + Cash ω ≤ w x + M ω + G ω + H ω) :
    (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
      Iic (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry

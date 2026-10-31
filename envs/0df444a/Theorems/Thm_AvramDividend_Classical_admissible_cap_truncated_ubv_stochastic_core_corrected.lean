-- Prove2me | Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_ubv_stochastic_core_corrected
-- name    : AvramDividend.Classical.admissible_cap_truncated_ubv_stochastic_core_corrected
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T13:17:32.703672+00:00
-- url     : https://prove2.me/theorems/429e17ca-5528-40b5-b593-7c03973d0706
-- title:
--   Corrected unbounded-variation finite-cap stochastic verification core with required zero boundary
-- statement:
--   Corrected form of the genuine original-process unbounded-variation truncated dividend bound. It restores the source paper's indispensable boundary assumption 0≤w(0), which was omitted from the published canonical target and whose absence has an accepted unconditional Gaussian counterexample and formal Type-0 negation. All other assumptions and the full discounted Stieltjes integral conclusion remain unchanged. Proving this statement still requires a same-path controlled Lévy-Itô/Itô-Meyer martingale localisation argument and Fatou passage. Publication is only a corrected Open declaration, not an assertion of verified stochastic calculus or automatic replacement of the original parent.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), w(0)≥0. Original false primary UUID ab47d6d9-7cd8-4e6a-b5b9-00d29941d9d4. Accepted unconditional all-cap Gaussian counterexample UUID 33fd15dc-8521-4cd8-9217-0701de90d703; accepted negation Type-0 UUID 520139dd-2607-40fc-8888-ecd422d4ebc7; Proved repaired boundary nonnegative cap UUID e3cd85ca-9e16-4b4c-8cee-e6de9dc7f20c. Formal body copied from canonical original and modified only by theorem name and hw0 binder.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.admissible_cap_truncated_ubv_stochastic_core_corrected
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry

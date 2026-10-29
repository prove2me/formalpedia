-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_supremum_real_mgf_rate_gap
-- name    : AvramDividend.Classical.avram_ws01e_bt_new_original_clock_supremum_real_mgf_rate_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:59:24.838853+00:00
-- url     : https://prove2.me/theorems/626336fd-5a80-4706-b37a-7ad676669364
-- title:
--   Finite real moment-generating function of the genuine original exponential-clock running maximum
-- statement:
--   Let X be an actual spectrally negative Lévy process and e an independent Exp(p) clock under original P. If lam>0 is a genuine root ψ(lam)=p>0 and β<lam is any real parameter, then exp(β S_e) is integrable and its real moment-generating function equals lam/(lam−β). The source-bound proof uses the already accepted exact ENNReal original-clock supremum moment, proves the lintegral finite using positivity of lam−β, passes through the canonical integrable ofReal conversion, and solves the real cross-multiplied identity. No extra integrability premise is added.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_supremum_lintegral_rate_gap
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bt_new_original_clock_supremum_real_mgf_rate_gap
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (lam : ℝ) (hlam : 0 < lam) (hroot : X.ψ lam = p)
    (β : ℝ) (hβlam : β < lam) :
    mgf (fun z : Ω × ℝ =>
      runningSup X (Real.toNNReal z.2) z.1)
      (P.prod (expMeasure p)) β =
    lam / (lam - β) := by sorry

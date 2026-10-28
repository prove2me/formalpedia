-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_positive_root_true_exp_clock_supremum_full_law_ws01d
-- name    : AvramDividend.Classical.levy_positive_root_true_exp_clock_supremum_full_law_ws01d
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T10:06:59.782522+00:00
-- url     : https://prove2.me/theorems/8ecbee20-1cc1-4009-989a-759f94ded31e
-- title:
--   Full exponential distribution of the genuine spectrally negative Lévy supremum at an independent exponential observation time
-- statement:
--   For a spectrally negative Lévy X under P, an independent real Exp(p) observation clock, p>0, and a positive Laplace root lam solving ψ(lam)=p, the pushforward probability law of the genuine running supremum at that observation time equals expMeasure(lam) exactly as a Borel measure on all ℝ. Extend the already-Proved strict positive threshold tail to all closed real half-lines: use probability complements at positive levels, continuity from above at zero, nonnegativity of the running supremum, and expMeasure's zero-level survival. This includes the atomlessness at the zero boundary without claiming pathwise strict positivity.
-- source:
--   Kuznetsov–Kyprianou–Rivero, The Theory of Scale Functions for Spectrally Negative Lévy Processes, section 2.1 equations (2.2)–(2.7), https://purehost.bath.ac.uk/ws/portalfiles/portal/9893933/Kyprianou_Levy_processes_2012.pdf ; canonical source theorem 42c23599-b0e9-4eb8-a585-115dd4774c93 and expMeasure strict tail 69bfdea1-9b67-42db-ab4b-e2473b94061f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_true_exp_clock_supremum_tail_ws01d
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_real

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_positive_root_true_exp_clock_supremum_full_law_ws01d
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (lam : ℝ) (hlam : 0 < lam) (hroot : X.ψ lam = p) :
    Measure.map (fun z : Ω × ℝ => runningSup X z.2.toNNReal z.1)
      (P.prod (ProbabilityTheory.expMeasure p)) =
    ProbabilityTheory.expMeasure lam := by sorry

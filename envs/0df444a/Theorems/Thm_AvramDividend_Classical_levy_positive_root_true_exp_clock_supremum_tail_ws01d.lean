-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_positive_root_true_exp_clock_supremum_tail_ws01d
-- name    : AvramDividend.Classical.levy_positive_root_true_exp_clock_supremum_tail_ws01d
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T08:31:46.418147+00:00
-- url     : https://prove2.me/theorems/42c23599-b0e9-4eb8-a585-115dd4774c93
-- title:
--   Exact upper tail of the genuine spectrally negative Lévy supremum at an independent exponential observation time
-- statement:
--   For a spectrally negative Lévy process under probability P and an independent real observation clock distributed according to expMeasure(p), with p>0, b>0 and positive Laplace-exponent root ψ(lam)=p, the genuine running supremum strictly exceeds b with product-measure probability exp(−lamb). The real clock is converted by toNNReal. This uses the exact strict first-upcrossing discounted transform, the strict-before-horizon event equivalence, and true exponential-clock survival, with the infinite-passage and zero-clock conventions retained.
-- source:
--   Kuznetsov, Kyprianou and Rivero (2013), The Theory of Scale Functions for Spectrally Negative Lévy Processes, §2.1 equations (2.2)–(2.7), https://purehost.bath.ac.uk/ws/portalfiles/portal/9893933/Kyprianou_Levy_processes_2012.pdf ; source-faithful Prove2Me accepted first-upcrossing 0da3763f-17e2-414b-ac46-9b9f2088aa29 and running-supremum event equivalence b626324c-8e00-4488-86d6-b7d63449435c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_exact_strict_upcrossing_discount
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_runningSup_gt_iff_strict_upcrossing_before_horizon
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_exp_clock_toNNReal_strict_tail

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_positive_root_true_exp_clock_supremum_tail_ws01d
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (lam : ℝ) (hlam : 0 < lam) (hroot : X.ψ lam = p)
    (b : ℝ) (hb : 0 < b) :
    (P.prod (ProbabilityTheory.expMeasure p))
      {z : Ω × ℝ | b < runningSup X z.2.toNNReal z.1} =
    ENNReal.ofReal (Real.exp (-(lam * b))) := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger62_original_bounded_stop_postpayment_exponential_L1
-- name    : AvramDividend.Classical.avram_gledger62_original_bounded_stop_postpayment_exponential_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:36:36.301674+00:00
-- url     : https://prove2.me/theorems/da65243c-6293-4913-aa21-06886b84bdb8
-- title:
--   Original bounded stopped Lévy upward exponential stays integrable after a nonnegative dividend offset
-- statement:
--   For the genuine original spectrally negative Lévy process at a bounded right-continuous stopping clock, subtracting a nonnegative postpayment dividend offset from the reserve preserves L1 integrability of the positive-parameter exponential. The source is the pinned original stopped Esscher moment lemma, with a deterministic bounded-clock discount correction. All measurability is tied to the original stopped random variable.
-- source:
--   Root-connected original clipped positive source gledger53: combine Proved 00c43baf original stopped Esscher integrability with nonnegative dividend offsets, finite clock and a.e. measurable postpayment exponentials.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightCont_bounded_stop_discounted_exp_integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger62_original_bounded_stop_postpayment_exponential_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (x : ℝ) (d : Ω → ℝ) (hd : ∀ ω, 0 ≤ d ω)
    (v : Ω → ℝ≥0)
    (hvmeas : Measurable (fun ω => (v ω : ℝ)))
    (hvstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (v ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hvbound : ∀ ω, v ω ≤ H)
    (hYmeas : AEStronglyMeasurable
      (fun ω => Real.exp (θ * (x + X.X (v ω) ω - d ω))) P) :
    Integrable (fun ω => Real.exp
      (θ * (x + X.X (v ω) ω - d ω))) P := by sorry

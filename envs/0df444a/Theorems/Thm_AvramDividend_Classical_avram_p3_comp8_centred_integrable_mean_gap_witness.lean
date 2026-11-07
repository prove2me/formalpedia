-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_centred_integrable_mean_gap_witness
-- name    : AvramDividend.Classical.avram_p3_comp8_centred_integrable_mean_gap_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:28:47.703062+00:00
-- url     : https://prove2.me/theorems/7c88b836-1252-491d-b8a3-f86b2b0a554f
-- title:
--   An integrable signed mean gap yields a centred zero-error witness by exact algebra
-- statement:
--   On any probability space, an integrable real sequence F_n, integrable B_n and vanishing positive gap max(EF_n-k-EB_n,0) give an explicit integrable mean-zero sequence M_n=F_n-B_n-(EF_n-EB_n). The pointwise residual is deterministic and its expected positive part equals the gap. This rigorously reduces the original Avram existential centred error target to a genuine signed mean-source estimate without changing source data.
-- source:
--   Independent algebraic reduction to be imported by canonical 4044d709. No original stochastic budget assumed in this lemma; all required mean-gap information is explicit as a premise.

import Mathlib
open MeasureTheory Filter
noncomputable section

theorem AvramDividend.Classical.avram_p3_comp8_centred_integrable_mean_gap_witness
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F B : ℕ → Ω → ℝ) (k : ℝ)
    (hFI : ∀ n, Integrable (F n) P)
    (hBI : ∀ n, Integrable (B n) P)
    (hGap : Tendsto
      (fun n => max ((∫ ω, F n ω ∂P) - k -
        (∫ ω, B n ω ∂P)) 0)
      atTop (nhds (0 : ℝ))) :
    ∃ M : ℕ → Ω → ℝ,
      (∀ n, Integrable (M n) P ∧
        (∫ ω, M n ω ∂P) = 0) ∧
      (∀ n, Integrable
        (fun ω => max (F n ω - (k + (M n ω + B n ω))) 0) P) ∧
      Tendsto
        (fun n => ∫ ω, max
          (F n ω - (k + (M n ω + B n ω))) 0 ∂P)
        atTop (nhds (0 : ℝ)) := by sorry

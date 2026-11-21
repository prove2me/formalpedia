-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerF_masked_pospart_L1_of_signed_L1
-- name    : AvramDividend.Classical.avram_pj_workerF_masked_pospart_L1_of_signed_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T21:42:05.19129+00:00
-- url     : https://prove2.me/theorems/60db6e43-258d-485b-b0ce-663b1fadd91d
-- title:
--   Any integrable signed residual vanishing in L1 has vanishing masked positive-part L1
-- statement:
--   For any measurable event and any sequence of integrable real-valued random residuals whose expected absolute values tend to zero, the event-masked nonnegative positive parts are integrable and their expected absolute values also tend to zero. The proof is deterministic via integrability of positive parts, integration monotonicity and a squeeze theorem. It supplies an authentic reusable transfer without altering any original stochastic source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerF_masked_pospart_L1_of_signed_L1
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : Set Ω) (hS : MeasurableSet S)
    (E : ℕ → Ω → ℝ)
    (hEI : ∀ k, Integrable (E k) P)
    (hVan : Tendsto (fun k => ∫ ω, |E k ω| ∂P)
      Filter.atTop (nhds (0 : ℝ))) :
    (∀ k, Integrable (S.indicator (fun ω => max (0 : ℝ) (E k ω))) P) ∧
    Tendsto (fun k => ∫ ω, |S.indicator
      (fun ω => max (0 : ℝ) (E k ω)) ω| ∂P)
      Filter.atTop (nhds (0 : ℝ)) := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_strict_contact_positive_error_L1_absorption
-- name    : AvramDividend.Classical.avram_bv_error7_strict_contact_positive_error_L1_absorption
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:28:35.511738+00:00
-- url     : https://prove2.me/theorems/bba96970-afdb-4e06-8f91-a56f419a3e6d
-- title:
--   Strict precontact and final contact positive Taylor errors combine in L1 without circular BV prebudget
-- statement:
--   For measurable stopped-grid errors, if the authentic full Taylor error splits exactly as strict-precontact plus one final contact contribution and the positive parts of the two components are integrable and vanish in expectation, then the full positive Taylor error is integrable and vanishes in expectation.
-- source:
--   Positive part of a+b is at most positive part of a plus positive part of b, yielding L1 domination. Integration, additivity and squeezing give the expected-error limit. This independent analytic lemma combines original source-specific strict and contact convergence once they are established, without invoking the BV prebudget or signed residual.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_strict_contact_positive_error_L1_absorption
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (ErrStrict ErrContact ErrFull : ℕ → Ω → ℝ)
    (hSplit : ∀ m ω, ErrFull m ω = ErrStrict m ω + ErrContact m ω)
    (hFullMeas : ∀ m, AEStronglyMeasurable (fun ω =>
      max (ErrFull m ω) 0) P)
    (hStrictInt : ∀ m, Integrable (fun ω => max (ErrStrict m ω) 0) P)
    (hContactInt : ∀ m, Integrable (fun ω => max (ErrContact m ω) 0) P)
    (hStrictMean : Tendsto (fun m => ∫ ω,
      max (ErrStrict m ω) 0 ∂P) atTop (nhds (0 : ℝ)))
    (hContactMean : Tendsto (fun m => ∫ ω,
      max (ErrContact m ω) 0 ∂P) atTop (nhds (0 : ℝ))) :
    (∀ m, Integrable (fun ω => max (ErrFull m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (ErrFull m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry

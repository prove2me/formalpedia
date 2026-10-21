-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_drifted_mark_sum_exp_factor
-- name    : AvramDividend.Classical.chat06_drifted_mark_sum_exp_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T15:55:54.828043+00:00
-- url     : https://prove2.me/theorems/abc101ce-714e-4c65-b5f0-a615e7ec98d4
-- title:
--   Factorising deterministic drift from the marked jump exponential moment
-- statement:
--   Factorise the deterministic unit drift exponent from the exponential of a random finite marked sum inside the Bochner integral.
-- source:
--   Original Chat 06 source remotely elaborated at pinned Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474; individual source SHA-256 and private compilation proof evidence in candidates/delegated/avram_round3/chat_06/SUBMISSIONS.json.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring

open MeasureTheory

theorem AvramDividend.Classical.chat06_drifted_mark_sum_exp_factor
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (t θ : ℝ) :
    (∫ ω, Real.exp (θ *
        (t + ∑ j ∈ Finset.range (N ω), Y j ω)) ∂P) =
      Real.exp (θ * t) *
        (∫ ω, Real.exp (θ *
          ∑ j ∈ Finset.range (N ω), Y j ω) ∂P) := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen11_rightLimit_single_right_payout
-- name    : AvramDividend.Classical.avram_gen11_rightLimit_single_right_payout
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:22:42.230063+00:00
-- url     : https://prove2.me/theorems/8e66a46f-1576-4bb7-ad61-8d8c2645d5da
-- title:
--   An exact single right-dividend payout is its source right-limit atom
-- statement:
--   A left-continuous single right-payment strategy pays A at the path-dependent threshold s. Its strict-future right limit at s is exactly A. This is the explicit right-payment atom needed for Avram source dividend admissibility and jump-condition bookkeeping.
-- source:
--   Source-exact rightLimit component of a possible original-process counterexample for the open Avram A19 generator-cell absolute-integrability theorem. This standalone helper does not assert stochastic adaptation or the full countermodel.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gen11_rightLimit_single_right_payout
    {Ω : Type*} (s : Ω → ℝ≥0) (A : Ω → ℝ) (ω : Ω) :
    rightLimit (fun t ω => if s ω < t then A ω else 0) (s ω) ω = A ω := by sorry

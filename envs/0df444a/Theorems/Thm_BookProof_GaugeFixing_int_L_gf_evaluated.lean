-- Prove2me | Theorems.Thm_BookProof_GaugeFixing_int_L_gf_evaluated
-- name    : BookProof.GaugeFixing.int_L_gf_evaluated
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T15:15:16.361719+00:00
-- url     : https://prove2.me/theorems/fb660369-d397-4307-93c4-5ed3b4bb3745
-- title:
--   The evaluated form of `int_L_gf_eq_zero`: the Lagrange-multiplier term and the ghost term cancel under the evaluation
-- statement:
--   The evaluated form of `int_L_gf_eq_zero`: the Lagrange-multiplier term and
--   the ghost term cancel under the evaluation.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.GaugeFixing.int_L_gf_evaluated` (module `BookProof.GaugeFixing`), line-linked source: `ChapterGaugeFixing.lean` lines 223–230.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGaugeFixing.lean#L223-L230

-- Generated from ChapterGaugeFixing.lean — theorem BookProof.GaugeFixing.int_L_gf_evaluated
import Mathlib
import Definitions.Def_ChapterGaugeFixing
open BookProof.GaugeFixing






















variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

theorem BookProof.GaugeFixing.int_L_gf_evaluated (I : BrstIntegral S) :
    I.int (S.sub (2, 0) (S.mul (1, 0) (1, 0) S.B (gaugeField S))
      (S.mul (1, -1) (1, 1) S.c_bar S.c)) = 0 := by sorry

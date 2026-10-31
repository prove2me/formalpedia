-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_06_vcstar_contDiffOn_two_of_cstar_top
-- name    : AvramDividend.Classical.avram_wave3_06_vcstar_contDiffOn_two_of_cstar_top
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T12:29:11.382845+00:00
-- url     : https://prove2.me/theorems/717ab230-508f-4c50-8cbe-0306117ac7b9
-- title:
--   Infinite cstar sentinel yields a C2 affine candidate value on positive reserves
-- statement:
--   For the canonical scale-function barrier definitions, an infinite cstar is sent to the real barrier zero. The candidate vcstar is then affine on every positive reserve, hence C2 there. This shows the standalone C2 disjunct in the root smoothness hypothesis cannot establish finite cstar and avoids circular proof routes.
-- source:
--   AvramDividend_Classical_ScaleFunction formal definitions of cstar, barrierValue and vcstar; direct definitional consequence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_06_vcstar_contDiffOn_two_of_cstar_top
    (W : ℝ → ℝ) (htop : cstar W = ⊤) :
    ContDiffOn ℝ 2 (vcstar W) (Ioi 0) := by sorry

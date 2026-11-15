-- Prove2me | Theorems.Thm_APFPaper5_K4_no_nonneg_flipped_part_record
-- name    : APFPaper5.K4.no_nonneg_flipped_part_record
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:54:18.048209+00:00
-- url     : https://prove2.me/theorems/81885800-fbcc-4114-8ed1-754bb6125e7c
-- title:
--   No nonneg flipped part record
-- statement:
--   No RecordWeights choice both agrees on every product with recDiag after first-part rateFlip and is nonnegative on every Joint state. The cost is the explicitly nonnegative quadratic recDiag, and agreement is for this observable. Do not replace it by a claim that every conceivable joint or physical extension is impossible.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2722-2735'}, {'path': 'source/Theorems/Thm_APFPaper5_K4_flipped_part.lean', 'sha256': '5d8e3b676dbe43788b4343511e91bfb7ee6fb9e005fa36c1f0b791987ef8e6a6', 'line': 87, 'declaration': 'APFPaper5.K4.no_nonneg_flipped_part_record'}]

import Definitions.Def_APFPaper5_K4_JointCarrier
import Definitions.Def_APFPaper5_K3_LinearOnTwoComponents
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace APFPaper5.K4
end APFPaper5.K4
open APFPaper5.K4
open APFPaper5.K3

theorem APFPaper5.K4.no_nonneg_flipped_part_record :
    ¬ ∃ w : RecordWeights,
      (∀ h k : Held2, linearRecord w (pair h k) = recDiag (pair (rateFlip h) k)) ∧
        ∀ p : Joint, 0 ≤ linearRecord w p := by sorry

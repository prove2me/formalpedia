-- Prove2me | Theorems.Thm_APFPaper5_K4_rateFlip_does_not_extend
-- name    : APFPaper5.K4.rateFlip_does_not_extend
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:55:50.371199+00:00
-- url     : https://prove2.me/theorems/4c8d8838-e39a-44cb-ba97-b46aba1cd727
-- title:
--   Rate flip has no specified joint-record extension
-- statement:
--   No Joint endomap and quadratic record weighting satisfy the defined ExtendsToJoint conditions for rateFlip: the forced minus-two record conflicts with recDiag nonnegativity. The cost is the explicitly nonnegative quadratic recDiag, and agreement is for this observable. Do not replace it by a claim that every conceivable joint or physical extension is impossible.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2722-2735'}, {'path': 'source/Theorems/Thm_APFPaper5_K4_flipped_part.lean', 'sha256': '5d8e3b676dbe43788b4343511e91bfb7ee6fb9e005fa36c1f0b791987ef8e6a6', 'line': 96, 'declaration': 'APFPaper5.K4.rateFlip_does_not_extend'}]

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

theorem APFPaper5.K4.rateFlip_does_not_extend : ¬ ExtendsToJoint rateFlip := by sorry

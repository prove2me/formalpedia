-- Prove2me | Theorems.Thm_APFPaper5_K4_jointFlip_recDiag
-- name    : APFPaper5.K4.jointFlip_recDiag
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:54:16.300027+00:00
-- url     : https://prove2.me/theorems/427c0317-7b8c-4c96-a4d1-c71409edbec6
-- title:
--   Joint Flip rec Diag
-- statement:
--   Supporting result: joint Flip rec Diag. It holds for exactly the parameters and hypotheses displayed in the attached formal statement. Every quadratic joint record agreeing on products with the first-part flip recDiag takes value minus two on antisym. Nonnegative such records and the defined extensions are impossible; identity extends. The cost is the explicitly nonnegative quadratic recDiag, and agreement is for this observable. Do not replace it by a claim that every conceivable joint or physical extension is impossible.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2722-2735'}, {'path': 'source/Theorems/Thm_APFPaper5_K4_flipped_part.lean', 'sha256': '5d8e3b676dbe43788b4343511e91bfb7ee6fb9e005fa36c1f0b791987ef8e6a6', 'line': 48, 'declaration': 'APFPaper5.K4.jointFlip_recDiag'}]

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

theorem APFPaper5.K4.jointFlip_recDiag (p : Joint) : recDiag (jointFlip p) = recDiag p := by sorry

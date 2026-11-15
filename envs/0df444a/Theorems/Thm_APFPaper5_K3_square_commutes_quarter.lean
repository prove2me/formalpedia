-- Prove2me | Theorems.Thm_APFPaper5_K3_square_commutes_quarter
-- name    : APFPaper5.K3.square_commutes_quarter
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:22:02.179208+00:00
-- url     : https://prove2.me/theorems/d92dc523-07de-4dea-9027-ebaf82149bfd
-- title:
--   Square commutes quarter
-- statement:
--   The square of a real-linear map satisfying CommonTurnUnseenAfter commutes with the common quarter turn. The result uses the full model orbit-profile definition. Arbitrary nonlinear maps and original physical admission are outside scope; record-factorization is a hypothesis, not the discrete FirstOrder predicate.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1800-1840,2006-2044'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_unseen_dichotomy.lean', 'sha256': 'cf1640df4abd1fbf8b44fb6bcdeeed36bcaab17860c36af8726c37678cf7c9b1', 'line': 228, 'declaration': 'APFPaper5.K3.square_commutes_quarter'}]

import Definitions.Def_APFPaper5_K3_HeldMaps
import Theorems.Thm_APFPaper5_K3_profile_preserving_linear_commutes_with_quarter
import Theorems.Thm_APFB01_quarter_record_descends
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.square_commutes_quarter (S : Held2 → Held2) (hlin : AdditiveHomogeneous S)
    (hun : CommonTurnUnseenAfter S) : CommutesWithQuarter (fun h => S (S h)) := by sorry

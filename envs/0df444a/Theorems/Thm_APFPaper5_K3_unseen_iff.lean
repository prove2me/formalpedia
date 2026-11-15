-- Prove2me | Theorems.Thm_APFPaper5_K3_unseen_iff
-- name    : APFPaper5.K3.unseen_iff
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:22:37.728741+00:00
-- url     : https://prove2.me/theorems/e87e398f-fa08-44ad-8f39-c162822b8762
-- title:
--   Unseen if and only if
-- statement:
--   For a real-linear Held2 map, common unit turns are invisible in its post-map plainAfterTurn profile exactly when it commutes or anticommutes with the common quarter turn. The result uses the full model orbit-profile definition. Arbitrary nonlinear maps and original physical admission are outside scope; record-factorization is a hypothesis, not the discrete FirstOrder predicate.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1800-1840,2006-2044'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_unseen_dichotomy.lean', 'sha256': 'cf1640df4abd1fbf8b44fb6bcdeeed36bcaab17860c36af8726c37678cf7c9b1', 'line': 223, 'declaration': 'APFPaper5.K3.unseen_iff'}]

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

theorem APFPaper5.K3.unseen_iff (T : Held2 → Held2) (hlin : AdditiveHomogeneous T) :
    CommonTurnUnseenAfter T ↔ CommutesWithQuarter T ∨ AnticommutesWithQuarter T := by sorry

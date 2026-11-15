-- Prove2me | Theorems.Thm_APFPaper5_K3_unseen_of_fixed_by_records
-- name    : APFPaper5.K3.unseen_of_fixed_by_records
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:23:23.431014+00:00
-- url     : https://prove2.me/theorems/3420c47c-75c4-41ea-9b12-f139e705155f
-- title:
--   Unseen of fixed by records
-- statement:
--   If equality of the two component costs and two cross terms before T implies equality of those four values after T, then common turns remain unseen after T. The result uses the full model orbit-profile definition. Arbitrary nonlinear maps and original physical admission are outside scope; record-factorization is a hypothesis, not the discrete FirstOrder predicate.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1800-1840,2006-2044'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_unseen_dichotomy.lean', 'sha256': 'cf1640df4abd1fbf8b44fb6bcdeeed36bcaab17860c36af8726c37678cf7c9b1', 'line': 238, 'declaration': 'APFPaper5.K3.unseen_of_fixed_by_records'}]

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

theorem APFPaper5.K3.unseen_of_fixed_by_records (T : Held2 → Held2)
    (hfo : ∀ h h' : Held2, recA h = recA h' → recB h = recB h' → crossRe h = crossRe h' →
      crossIm h = crossIm h' →
      recA (T h) = recA (T h') ∧ recB (T h) = recB (T h') ∧ crossRe (T h) = crossRe (T h') ∧
        crossIm (T h) = crossIm (T h')) :
    CommonTurnUnseenAfter T := by sorry

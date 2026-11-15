-- Prove2me | Theorems.Thm_APFPaper5_K3_unseen_of_anticommutes
-- name    : APFPaper5.K3.unseen_of_anticommutes
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:22:37.216707+00:00
-- url     : https://prove2.me/theorems/4fd4cc22-ec30-489d-9818-8d89405f564c
-- title:
--   Unseen of anticommutes
-- statement:
--   Supporting result: unseen of anticommutes. It holds for exactly the parameters and hypotheses displayed in the attached formal statement. For real-linear Held2 maps, common-turn invisibility in plainAfterTurn is equivalent to commuting or anticommuting with J. Their squares commute. Four-record equality and record-factorization lemmas expose the chosen equivalence. The result uses the full model orbit-profile definition. Arbitrary nonlinear maps and original physical admission are outside scope; record-factorization is a hypothesis, not the discrete FirstOrder predicate.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1800-1840,2006-2044'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_unseen_dichotomy.lean', 'sha256': 'cf1640df4abd1fbf8b44fb6bcdeeed36bcaab17860c36af8726c37678cf7c9b1', 'line': 215, 'declaration': 'APFPaper5.K3.unseen_of_anticommutes'}]

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

theorem APFPaper5.K3.unseen_of_anticommutes (T : Held2 → Held2) (hlin : AdditiveHomogeneous T)
    (ha : AnticommutesWithQuarter T) : CommonTurnUnseenAfter T := by sorry

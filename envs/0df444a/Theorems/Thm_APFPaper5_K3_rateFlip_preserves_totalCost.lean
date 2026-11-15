-- Prove2me | Theorems.Thm_APFPaper5_K3_rateFlip_preserves_totalCost
-- name    : APFPaper5.K3.rateFlip_preserves_totalCost
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:41:58.436216+00:00
-- url     : https://prove2.me/theorems/b838f8ef-9d4b-4240-81ac-1c38c360661b
-- title:
--   Rate Flip preserves total Cost
-- statement:
--   Supporting result: rate Flip preserves total Cost. It holds for exactly the parameters and hypotheses displayed in the attached formal statement. Generated maps are real-linear, preserve total squared cost, commute with common turns and keep them unseen. A one-plane turn and rateFlip illustrate distinct failures of generated membership. Unit-pair premises are retained for norm preservation. Common-turn invisibility is relative to plainAfterTurn, not universal physical invisibility.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1862-1888,2006-2044'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_built_from_turns.lean', 'sha256': '15f8264d9ccad85d50a21b91a10b5256ab28f26242f67aca7a349d739def10a4', 'line': 127, 'declaration': 'APFPaper5.K3.rateFlip_preserves_totalCost'}]

import Definitions.Def_APFPaper5_K3_HeldMaps
import Theorems.Thm_APFPaper5_K3_records_of_plainAfterTurn_eq
import Theorems.Thm_APFPaper5_K3_plainAfterTurn_eq_iff_records
import Theorems.Thm_APFPaper5_K3_pair_dichotomy
import Theorems.Thm_APFPaper5_K3_unseen_dichotomy
import Theorems.Thm_APFPaper5_K3_unseen_of_anticommutes
import Theorems.Thm_APFPaper5_K3_unseen_iff
import Theorems.Thm_APFPaper5_K3_square_commutes_quarter
import Theorems.Thm_APFPaper5_K3_unseen_of_fixed_by_records
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.rateFlip_preserves_totalCost : PreservesTotalCost rateFlip := by sorry

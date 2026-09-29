-- Prove2me | Theorems.Thm_CKLaneA3X_Step027_polynomial_identity
-- name    : CKLaneA3X.Step027.polynomial_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T03:24:26.930474+00:00
-- url     : https://prove2.me/theorems/0678dacb-e5b6-45ee-b151-6f6e5a1cb510
-- title:
--   The complete A3X square polynomial matches its certificate
-- statement:
--   The exact square of D_Us.P truncated to 24 rows equals the complete D_UsUs.P certificate. This is the kernel-equivalent compact form of Step027’s polynomial premise. It combines all 24 proved row equalities; the original analytic theorem retains its separate genuine input hypothesis.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/Step027.lean#L15

import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_Step027_data_functions

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open CKLaneA3X

theorem CKLaneA3X.Step027.polynomial_identity : (TPoly.mulT D_Us.P D_Us.P 24) = D_UsUs.P := by sorry

-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_dom_down
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_dom_down
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:23:18.732372+00:00
-- url     : https://prove2.me/theorems/5886a6b8-b668-4d10-b3e0-fb6c34af7c79
-- title:
--   Column Families: qs dom down
-- statement:
--   The Column Families construction uses the qs dom down property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsColHStrip.lean#L28-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsColHStrip.lean#L28-L36

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
omit [NeZero n]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_dom_down {lam kap : Fin n → ℤ} {b : ℕ} (hk : Dominant kap) (hs : HStrip lam kap b) : Dominant lam := by sorry

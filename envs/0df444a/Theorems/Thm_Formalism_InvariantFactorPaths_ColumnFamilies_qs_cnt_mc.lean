-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_cnt_mc
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_cnt_mc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:38:00.495589+00:00
-- url     : https://prove2.me/theorems/646bef61-8d67-454f-9ea8-e9838cabde62
-- title:
--   Column Families: qs cnt mc
-- statement:
--   The Column Families construction uses the qs cnt mc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsColHStrip.lean#L76-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsColHStrip.lean#L76-L98

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_cnt_mc {lam kap : Fin n → ℤ} {b : ℕ} (hl : Dominant lam) (hk : Dominant kap) (hs : HStrip lam kap b)
    (x : Fin n) : ((qs_cnt (qs_mc lam kap) x : ℕ) : ℤ) = kap x - lam x := by sorry

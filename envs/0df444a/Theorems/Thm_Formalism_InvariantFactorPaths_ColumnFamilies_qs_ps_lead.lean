-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_ps_lead
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_ps_lead
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:29:05.423636+00:00
-- url     : https://prove2.me/theorems/d216b48a-9733-4909-b9cd-79c80fb1924e
-- title:
--   Column Families: qs ps lead
-- statement:
--   The Column Families construction uses the qs ps lead property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SymStrip.lean#L137-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SymStrip.lean#L137-L150

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymStrip
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_card_D

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_ps_lead (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) (hs : HStrip mu nu b) :
    qs_ps b mu nu (canT mu, qs_mon (qs_card_D hmu hnu hs) (qs_mc mu nu)) (canT nu) = 1 := by sorry

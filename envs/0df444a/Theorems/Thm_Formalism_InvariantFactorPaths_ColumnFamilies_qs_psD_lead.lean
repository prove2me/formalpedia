-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_psD_lead
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_psD_lead
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:29:08.5602+00:00
-- url     : https://prove2.me/theorems/fecf1ba8-a8f6-43ac-b012-44c88623fb6c
-- title:
--   Column Families: qs ps D lead
-- statement:
--   The Column Families construction uses the qs ps D lead property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SymDStrip.lean#L143-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SymDStrip.lean#L143-L157

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymStrip
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymDStrip
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_psD_lead (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) (hs : HStrip nu mu b) :
    qs_psD b mu nu (canT mu, qs_mon (qs_card_D hnu hmu hs) (qs_mc nu mu)) (canT nu) = 1 := by sorry

-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_can_sub
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qr_can_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:17.976479+00:00
-- url     : https://prove2.me/theorems/66485b59-c3a9-41dc-827f-1cdc29ee90e9
-- title:
--   Column Families: qr can sub
-- statement:
--   The Column Families construction uses the qr can sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestWeightIntegral.lean#L157-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestWeightIntegral.lean#L157-L161

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {m : ℕ} [NeZero m] {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ}

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qr_can_sub (c : ℤ) : (qr_can nu (c + 1)).1 ⊆ (qr_can nu c).1 := by sorry

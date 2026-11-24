-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_ext_surj
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qr_ext_surj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:45.468185+00:00
-- url     : https://prove2.me/theorems/0f8e8cd2-4342-4657-99c2-e70c75aa8740
-- title:
--   Column Families: qr ext surj
-- statement:
--   The Column Families construction uses the qr ext surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestWeightSpaceFinite.lean#L41-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestWeightSpaceFinite.lean#L41-L46

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
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
variable {m : ℕ} (e : Prop) [Decidable e] (S : Finset (Fin m))

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qr_ext_surj (K : Finset (Fin (m + 1))) (h : Fin.last m ∈ K ↔ e) :
    K = qr_ext e (univ.filter fun a : Fin m => a.castSucc ∈ K) := by sorry

-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_filter_last
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qr_filter_last
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:46.696318+00:00
-- url     : https://prove2.me/theorems/9d3c4f10-051d-473c-86d3-2b376fac7c0b
-- title:
--   Column Families: qr filter last
-- statement:
--   The Column Families construction uses the qr filter last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestWeightSpaceFinite.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestWeightSpaceFinite.lean#L61-L63

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qr_filter_last : ((qr_ext e S).filter (· ≤ Fin.last m)) = qr_ext e S := by sorry

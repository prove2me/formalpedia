-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_D_nondom
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qk_D_nondom
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:22:14.150699+00:00
-- url     : https://prove2.me/theorems/db6a1b33-0a4a-43be-aee1-5b5002628c4a
-- title:
--   Column Families: qk D nondom
-- statement:
--   The Column Families construction uses the qk D nondom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CntLam.lean#L78-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CntLam.lean#L78-L93

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntSym
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QkDetExpand
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_Branch
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_WeylGT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CntLam
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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases (dGT)

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qk_D_nondom {n : ℕ} {mu : Fin n → ℤ} (hmu : Dominant mu) (s : Finset (Fin n))
    (h : ¬ Dominant (qk_add mu s)) : qk_D (qk_v (qk_add mu s)) = 0 := by sorry

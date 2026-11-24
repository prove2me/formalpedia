-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_sel_add
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qk_sel_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:22:14.305185+00:00
-- url     : https://prove2.me/theorems/8f01adf5-add4-4500-8c48-10f875b03349
-- title:
--   Column Families: qk sel add
-- statement:
--   The Column Families construction uses the qk sel add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CntLam.lean#L118-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CntLam.lean#L118-L121

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qk_sel_add {n : ℕ} (mu : Fin n → ℤ) (s : Finset (Fin n)) :
    (univ.filter fun a => qk_add mu s a = mu a + 1) = s := by sorry

-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_add_sel
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qk_add_sel
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:24.874818+00:00
-- url     : https://prove2.me/theorems/54f70b81-e4a9-4338-8ddf-6893d6f1c195
-- title:
--   Column Families: qk add sel
-- statement:
--   The Column Families construction uses the qk add sel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CntLam.lean#L108-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CntLam.lean#L108-L116

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qk_add_sel {n : ℕ} {mu nu : Fin n → ℤ} (h : ∀ a, mu a ≤ nu a ∧ nu a ≤ mu a + 1) :
    qk_add mu (univ.filter fun a => nu a = mu a + 1) = nu := by sorry

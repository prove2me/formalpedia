-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qk_weyl
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qk_weyl
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:22:32.621807+00:00
-- url     : https://prove2.me/theorems/10c30b29-bef4-4777-87ad-1be7e8254e23
-- title:
--   Column Families: qk weyl
-- statement:
--   The Column Families construction uses the qk weyl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CntLam.lean#L46-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CntLam.lean#L46-L56

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qk_weyl {n : ℕ} (mu : Fin n → ℤ) :
    Formalism.InvariantFactorPaths.BranchingDimensions.weylDim n (Formalism.InvariantFactorPaths.BranchingDimensions.extW mu) * vandermondeDenominator n = qk_D (qk_v mu) := by sorry

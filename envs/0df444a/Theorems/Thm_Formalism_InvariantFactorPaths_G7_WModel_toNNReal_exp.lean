-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_toNNReal_exp
-- name    : Formalism.InvariantFactorPaths.G7.WModel.toNNReal_exp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:29:02.621526+00:00
-- url     : https://prove2.me/theorems/ce7a0cda-6d91-4409-8934-73d7d9f80444
-- title:
--   WModel: to NNReal exp
-- statement:
--   The WModel construction uses the to NNReal exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/WModel.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/WModel.lean#L35-L40

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementW
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_WittTeichmullerRoot
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_WModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NNReal
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.InvariantFactorPaths.G7.WModel
variable (p : ℕ) [hp : Fact p.Prime]

theorem Formalism.InvariantFactorPaths.G7.WModel.toNNReal_exp {e : ℝ≥0} (he : e ≠ 0) (n : ℤ) :
    WithZeroMulInt.toNNReal he (WithZero.exp n) = e ^ n := by sorry

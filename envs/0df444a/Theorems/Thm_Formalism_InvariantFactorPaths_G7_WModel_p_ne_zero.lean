-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_p_ne_zero
-- name    : Formalism.InvariantFactorPaths.G7.WModel.p_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:56:30.299078+00:00
-- url     : https://prove2.me/theorems/386f4fd2-fc56-4274-b4b1-376d8d6c189e
-- title:
--   WModel: p ne zero
-- statement:
--   The WModel construction uses the p ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/WModel.lean#L66-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/WModel.lean#L66-L73

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

theorem Formalism.InvariantFactorPaths.G7.WModel.p_ne_zero : (p : KK p) ≠ 0 := by sorry

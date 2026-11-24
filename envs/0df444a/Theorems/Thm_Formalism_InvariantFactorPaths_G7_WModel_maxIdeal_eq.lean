-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_maxIdeal_eq
-- name    : Formalism.InvariantFactorPaths.G7.WModel.maxIdeal_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:39.296411+00:00
-- url     : https://prove2.me/theorems/f9e6a6f8-cdf2-4588-882b-c8180a944d5d
-- title:
--   WModel: max Ideal eq
-- statement:
--   The WModel construction uses the max Ideal eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/WModel.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/WModel.lean#L25-L27

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

theorem Formalism.InvariantFactorPaths.G7.WModel.maxIdeal_eq : (IsDiscreteValuationRing.maximalIdeal (WW p)).asIdeal =
    Ideal.span {(p : WW p)} := by sorry

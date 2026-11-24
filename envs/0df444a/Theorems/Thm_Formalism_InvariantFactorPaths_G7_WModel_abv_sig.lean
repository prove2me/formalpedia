-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_abv_sig
-- name    : Formalism.InvariantFactorPaths.G7.WModel.abv_sig
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:56:25.341233+00:00
-- url     : https://prove2.me/theorems/14283a20-079d-48ee-a944-50bcf79eaea9
-- title:
--   WModel: abv sig
-- statement:
--   The WModel construction uses the abv sig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/WModel.lean#L142-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/WModel.lean#L142-L148

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

theorem Formalism.InvariantFactorPaths.G7.WModel.abv_sig (a : KK p) (ha : abv p a ≤ 1) : abv p (sig p a - a ^ p) ≤ (p : ℝ)⁻¹ := by sorry

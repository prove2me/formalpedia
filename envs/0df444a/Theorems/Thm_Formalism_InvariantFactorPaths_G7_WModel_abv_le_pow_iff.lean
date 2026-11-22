-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_abv_le_pow_iff
-- name    : Formalism.InvariantFactorPaths.G7.WModel.abv_le_pow_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:08:09.943118+00:00
-- url     : https://prove2.me/theorems/7c2d75aa-05c2-4610-824f-3c3c8481afba
-- title:
--   WModel: abv le pow iff
-- statement:
--   The WModel construction uses the abv le pow iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/WModel.lean#L102-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/WModel.lean#L102-L119

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

theorem Formalism.InvariantFactorPaths.G7.WModel.abv_le_pow_iff (N : ℕ) (x : KK p) : abv p x ≤ ((p : ℝ)⁻¹) ^ N ↔
    ∃ w : WW p, x = (p : KK p) ^ N * algebraMap (WW p) (KK p) w := by sorry

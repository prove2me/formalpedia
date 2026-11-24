-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_digits_sum_le_lgN
-- name    : Formalism.InvariantFactorPaths.G7.digits_sum_le_lgN
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:29:47.383219+00:00
-- url     : https://prove2.me/theorems/b655517f-ae94-40d2-a630-800e80591e33
-- title:
--   G7: digits sum le lg N
-- statement:
--   The G7 construction uses the digits sum le lg N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ABArith.lean#L23-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ABArith.lean#L23-L33

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_PathBasisOfCount
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_QuadraticExponentIdentity
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ABArith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.GrowthSums (gamP rhoP gainG excessGain)

theorem Formalism.InvariantFactorPaths.G7.digits_sum_le_lgN (p m : ℕ) (hp : 1 < p) :
    (Nat.digits p m).sum ≤ (p - 1) * lgN p m := by sorry

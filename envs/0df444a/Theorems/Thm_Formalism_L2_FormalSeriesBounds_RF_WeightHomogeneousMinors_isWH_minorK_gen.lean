-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousMinors_isWH_minorK_gen
-- name    : Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.isWH_minorK_gen
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:53:11.581314+00:00
-- url     : https://prove2.me/theorems/5de7ca74-6770-4f37-81a9-778ec35b6837
-- title:
--   Weight Homogeneous Minors: is WH minor K gen
-- statement:
--   The Weight Homogeneous Minors construction uses the is WH minor K gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneRowDegrees.lean#L40-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneRowDegrees.lean#L40-L57

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowDegrees
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
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
open Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
variable {R : Type} [CommRing R]

theorem Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.isWH_minorK_gen {N N' k : ℕ} {w : Fin N × Fin N' → ℕ} (v : Fin N' → ℕ) (hw : ∀ x, w x = v x.2)
    (h : k ≤ N ∧ k ≤ N') :
    IsWeightedHomogeneous w (minorK R N N' k) (∑ c : Fin k, v (Fin.castLE h.2 c)) := by sorry

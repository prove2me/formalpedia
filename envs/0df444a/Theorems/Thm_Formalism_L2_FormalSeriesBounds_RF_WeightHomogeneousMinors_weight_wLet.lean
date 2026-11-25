-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousMinors_weight_wLet
-- name    : Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.weight_wLet
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:53:38.725173+00:00
-- url     : https://prove2.me/theorems/fc703215-cae7-4a5b-ac12-faf32cbd11ea
-- title:
--   Weight Homogeneous Minors: weight w Let
-- statement:
--   The Weight Homogeneous Minors construction uses the weight w Let property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneRowDegrees.lean#L94-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneRowDegrees.lean#L94-L104

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
variable {T : Type} (r : T → ℕ) (n : ℕ)

theorem Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.weight_wLet (σ : T) (c0 : Fin (r σ)) (m : Letter T r n →₀ ℕ) :
    Finsupp.weight (wLet r n σ c0) m = ∑ b : Fin n, m ⟨σ, c0, b⟩ := by sorry

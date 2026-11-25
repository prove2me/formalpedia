-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousMinors_wLet_mk
-- name    : Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.wLet_mk
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:52:37.733797+00:00
-- url     : https://prove2.me/theorems/b6d90593-9871-4631-af7a-431b3d0ceb88
-- title:
--   Weight Homogeneous Minors: w Let mk
-- statement:
--   The Weight Homogeneous Minors construction uses the w Let mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneRowDegrees.lean#L118-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneRowDegrees.lean#L118-L126

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
variable {r n}

theorem Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.wLet_mk (σ : T) (c0 : Fin (r σ)) (τ : T) (c : Fin (r τ)) (ρ : Fin n) :
    wLet r n σ c0 ⟨τ, (c, ρ)⟩ = if (⟨τ, c⟩ : Σ σ, Fin (r σ)) = ⟨σ, c0⟩ then 1 else 0 := by sorry

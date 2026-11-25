-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousLetters_num_mon
-- name    : Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters.num_mon
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:15:52.391935+00:00
-- url     : https://prove2.me/theorems/d5a2c7fe-4d2e-4125-b020-bff2962e2daa
-- title:
--   Weight Homogeneous Letters: num mon
-- statement:
--   The Weight Homogeneous Letters construction uses the num mon property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/IsWHLetterMinorK.lean#L81-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/IsWHLetterMinorK.lean#L81-L101

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCInv
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowDegrees
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IsWHLetterMinorK
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousMinors_num_mon

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
open Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters
open WeightHomogeneousMinors
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
  (X : RowData C V d I J) (F : Flag X) (idx : ∀ g, I g → ℕ) (std : ∀ g t (c : Fin (X.rkF g t)), idx g (F.en g t c) = c.val)

theorem Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousLetters.num_mon (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (e : ZMod d → ℕ → ℕ) (N : ℕ) :
    (∑ t : ZMod d, ∑ k ∈ Finset.Icc 1 (min N (X.rkF g t)),
      e t k • (if k ≤ N ∧ k ≤ X.rkF g t ∧ (g = g0 ∧ t = t0) ∧ c0 < k then 1 else 0)) =
      ∑ k ∈ Finset.Icc (c0 + 1) (X.rkF g0 t0),
        (if g0 = g ∧ 1 ≤ k ∧ k ≤ min N (X.rkF g t0) then e t0 k else 0) := by sorry

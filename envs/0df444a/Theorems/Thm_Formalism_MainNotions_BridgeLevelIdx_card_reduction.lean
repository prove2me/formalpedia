-- Prove2me | Theorems.Thm_Formalism_MainNotions_BridgeLevelIdx_card_reduction
-- name    : Formalism.MainNotions.BridgeLevelIdx.card_reduction
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:41:56.64925+00:00
-- url     : https://prove2.me/theorems/621f5c51-86d5-46df-9aeb-cf5ab2be6170
-- title:
--   Bridge Level Idx: card reduction
-- statement:
--   The Bridge Level Idx construction uses the card reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelIdx.lean#L78-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelIdx.lean#L78-L102

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelIdx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLevelIdx
open MeasureTheory Formalism.MainNotions.S Matrix
open scoped ENNReal TensorProduct
variable (I : AutInst)
variable {I}

theorem Formalism.MainNotions.BridgeLevelIdx.card_reduction {g : ℕ} (hg : 1 ≤ g) (hG : LevelGen I g) :
    ∃ (α : Type) (_ : Fintype α) (ρ : I.Gf → α), Fintype.card α ≤ g ^ (2 * I.n ^ 2 * I.f) ∧
      ∀ x ∈ I.Kset, ∀ x' ∈ I.Kset, ρ x = ρ x' → x⁻¹ * x' ∈ I.Kg g := by sorry

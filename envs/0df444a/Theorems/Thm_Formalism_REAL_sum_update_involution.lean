-- Prove2me | Theorems.Thm_Formalism_REAL_sum_update_involution
-- name    : Formalism.REAL.sum_update_involution
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:26:39.21802+00:00
-- url     : https://prove2.me/theorems/2ff34e26-09da-4183-8945-03f614cd5b41
-- title:
--   REAL: sum update involution
-- statement:
--   The REAL construction uses the sum update involution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L43-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L43-L54

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n j : ℕ}

theorem Formalism.REAL.sum_update_involution {X M : Type*} [Fintype X] [DecidableEq X] [AddCommMonoid M] (i : Fin j)
    (σ : X → X) (hσ : ∀ x, σ (σ x) = x) (P : X → Prop) [DecidablePred P]
    (f : (Fin j → X) → (Fin j → X) → M) :
    ∑ α : Fin j → X, (if P (α i) then f (Function.update α i (σ (α i))) α else 0) =
      ∑ β : Fin j → X, (if P (σ (β i)) then f β (Function.update β i (σ (β i))) else 0) := by sorry

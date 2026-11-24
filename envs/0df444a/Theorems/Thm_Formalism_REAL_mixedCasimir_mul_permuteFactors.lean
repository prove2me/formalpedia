-- Prove2me | Theorems.Thm_Formalism_REAL_mixedCasimir_mul_permuteFactors
-- name    : Formalism.REAL.mixedCasimir_mul_permuteFactors
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:24:57.315481+00:00
-- url     : https://prove2.me/theorems/a6750339-37cf-4374-ada7-98a9f18fd5dc
-- title:
--   REAL: mixed Casimir mul permute Factors
-- statement:
--   The REAL construction uses the mixed Casimir mul permute Factors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L278-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L278-L284

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

theorem Formalism.REAL.mixedCasimir_mul_permuteFactors (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (σ : Equiv.Perm (Fin j))
    (i : Fin j) : OmS ε E i * permArr V n σ = permArr V n σ * OmS ε E (σ.symm i) := by sorry

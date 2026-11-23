-- Prove2me | Theorems.Thm_Formalism_REAL_factorAction_mul_permuteFactors
-- name    : Formalism.REAL.factorAction_mul_permuteFactors
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:16.443609+00:00
-- url     : https://prove2.me/theorems/19530bc9-c62d-47bb-965c-a7068e1f61a8
-- title:
--   REAL: factor Action mul permute Factors
-- statement:
--   The REAL construction uses the factor Action mul permute Factors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L267-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L267-L271

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

theorem Formalism.REAL.factorAction_mul_permuteFactors (σ : Equiv.Perm (Fin j)) (i : Fin j) (c d : Fin n) :
    factorAction (V := V) i c d * permArr V n σ = permArr V n σ * factorAction (σ.symm i) c d := by sorry

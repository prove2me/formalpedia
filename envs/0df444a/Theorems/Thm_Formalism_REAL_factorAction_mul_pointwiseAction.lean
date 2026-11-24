-- Prove2me | Theorems.Thm_Formalism_REAL_factorAction_mul_pointwiseAction
-- name    : Formalism.REAL.factorAction_mul_pointwiseAction
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:21:28.781594+00:00
-- url     : https://prove2.me/theorems/a6b35d6d-0686-489e-b46d-ef16bdfc5e5a
-- title:
--   REAL: factor Action mul pointwise Action
-- statement:
--   The REAL construction uses the factor Action mul pointwise Action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L167-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L167-L172

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

theorem Formalism.REAL.factorAction_mul_pointwiseAction (E : Fin n → Fin n → Module.End ℂ V) (i : Fin j) (a b c d : Fin n) :
    factorAction (V := V) i a b * ptE (j := j) E c d = ptE E c d * factorAction i a b := by sorry

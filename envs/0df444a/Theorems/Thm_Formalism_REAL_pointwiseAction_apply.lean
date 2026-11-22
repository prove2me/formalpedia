-- Prove2me | Theorems.Thm_Formalism_REAL_pointwiseAction_apply
-- name    : Formalism.REAL.pointwiseAction_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:00:17.35144+00:00
-- url     : https://prove2.me/theorems/04f904bf-ea79-4759-b598-8161232ca512
-- title:
--   REAL: pointwise Action apply
-- statement:
--   The REAL construction uses the pointwise Action apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L22-L24

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

theorem Formalism.REAL.pointwiseAction_apply (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) (F : Arr V n j)
    (α : Fin j → Fin n × Fin n) : ptE E c d F α = E c d (F α) := by sorry

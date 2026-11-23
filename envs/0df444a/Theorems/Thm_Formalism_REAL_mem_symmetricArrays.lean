-- Prove2me | Theorems.Thm_Formalism_REAL_mem_symmetricArrays
-- name    : Formalism.REAL.mem_symmetricArrays
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:26.83381+00:00
-- url     : https://prove2.me/theorems/faf9bc84-ea25-4fe2-8938-0b4908f35e23
-- title:
--   REAL: mem symmetric Arrays
-- statement:
--   The REAL construction uses the mem symmetric Arrays property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L292-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L292-L294

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

theorem Formalism.REAL.mem_symmetricArrays (F : Arr V n j) :
    F ∈ symSub V n j ↔ ∀ σ : Equiv.Perm (Fin j), permArr V n σ F = F := by sorry

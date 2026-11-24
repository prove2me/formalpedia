-- Prove2me | Theorems.Thm_Formalism_REAL_height_word_shift_nonneg
-- name    : Formalism.REAL.height_word_shift_nonneg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:21:19.855106+00:00
-- url     : https://prove2.me/theorems/98223ca3-821f-46ae-807f-f06fd7b4b52b
-- title:
--   REAL: height word shift nonneg
-- statement:
--   The REAL construction uses the height word shift nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CompactCasimirHighestWeight.lean#L79-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CompactCasimirHighestWeight.lean#L79-L90

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
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
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}

theorem Formalism.REAL.height_word_shift_nonneg {m : ℕ} (w : List (Fin m × Fin m)) (hw : ∀ p ∈ w, p.2 < p.1) :
    0 ≤ heightFunctional (wordWeightShift w) ∧ (w ≠ [] → 0 < heightFunctional (wordWeightShift w)) := by sorry

-- Prove2me | Theorems.Thm_Formalism_REAL_drop_ofFn_congr
-- name    : Formalism.REAL.drop_ofFn_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:13.645807+00:00
-- url     : https://prove2.me/theorems/920908c5-e954-4d54-a18d-abb197ea9ed0
-- title:
--   REAL: drop of Fn congr
-- statement:
--   The REAL construction uses the drop of Fn congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ShiftedGeneratorEqIteSmulAdd.lean#L93-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ShiftedGeneratorEqIteSmulAdd.lean#L93-L101

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL

theorem Formalism.REAL.drop_ofFn_congr {α : Type*} {t : ℕ} (f g : Fin t → α) (i : ℕ)
    (h : ∀ k : Fin t, i ≤ (k : ℕ) → f k = g k) :
    (List.ofFn f).drop i = (List.ofFn g).drop i := by sorry

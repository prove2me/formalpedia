-- Prove2me | Theorems.Thm_Formalism_REAL_take_ofFn_congr
-- name    : Formalism.REAL.take_ofFn_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:18.819772+00:00
-- url     : https://prove2.me/theorems/233064b9-3212-4308-929b-67091b425c7d
-- title:
--   REAL: take of Fn congr
-- statement:
--   The REAL construction uses the take of Fn congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ShiftedGeneratorEqIteSmulAdd.lean#L81-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/ShiftedGeneratorEqIteSmulAdd.lean#L81-L91

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

theorem Formalism.REAL.take_ofFn_congr {α : Type*} {t : ℕ} (f g : Fin t → α) (i : ℕ)
    (h : ∀ k : Fin t, (k : ℕ) < i → f k = g k) :
    (List.ofFn f).take i = (List.ofFn g).take i := by sorry

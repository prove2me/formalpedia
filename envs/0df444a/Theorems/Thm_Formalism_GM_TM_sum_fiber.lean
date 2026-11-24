-- Prove2me | Theorems.Thm_Formalism_GM_TM_sum_fiber
-- name    : Formalism.GM.TM.sum_fiber
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:47.56912+00:00
-- url     : https://prove2.me/theorems/ad548440-6c3c-4e09-b0b8-e4b0e87b7f87
-- title:
--   TM: sum fiber
-- statement:
--   The TM construction uses the sum fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L222-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L222-L254

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open Finset

theorem Formalism.GM.TM.sum_fiber {t : ℕ} (s : Fin t → Finset ℕ) (g : (Fin t → ℕ) → ℝ) (i : Fin t) :
    ∑ n ∈ Fintype.piFinset s, ∑ y ∈ s i, g (Function.update n i y) =
      (s i).card * ∑ n ∈ Fintype.piFinset s, g n := by sorry

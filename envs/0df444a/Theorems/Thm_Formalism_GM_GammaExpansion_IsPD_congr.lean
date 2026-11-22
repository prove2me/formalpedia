-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_IsPD_congr
-- name    : Formalism.GM.GammaExpansion.IsPD.congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:40:45.724292+00:00
-- url     : https://prove2.me/theorems/b51f67a6-c9a5-42d3-bbf8-c05c1d7f6c1b
-- title:
--   Is PD: congr
-- statement:
--   The Is PD construction uses the congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L696-L699
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L696-L699

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open Polynomial Finset
variable {k : Type} [Field k] [CharZero k]

theorem Formalism.GM.GammaExpansion.IsPD.congr {N0 d : ℕ} {g g' : ℕ → k} (h : IsPD N0 d g) (hg : ∀ n, N0 ≤ n → g' n = g n) :
    IsPD N0 d g' := by sorry

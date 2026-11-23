-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_IsPD_choose_add
-- name    : Formalism.GM.GammaExpansion.IsPD.choose_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:49.25313+00:00
-- url     : https://prove2.me/theorems/455e2643-6cd1-4a1b-be2c-57b85dd24238
-- title:
--   Is PD: choose add
-- statement:
--   The Is PD construction uses the choose add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L735-L742
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L735-L742

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

theorem Formalism.GM.GammaExpansion.IsPD.choose_add (N0 c t : ℕ) : IsPD N0 t (fun n => (((n + c).choose t : ℕ) : k)) := by sorry

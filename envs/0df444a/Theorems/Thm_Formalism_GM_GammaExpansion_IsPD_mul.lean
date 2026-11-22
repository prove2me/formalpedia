-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_IsPD_mul
-- name    : Formalism.GM.GammaExpansion.IsPD.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:40:56.484798+00:00
-- url     : https://prove2.me/theorems/373a9eb6-e7ba-44bc-9183-fb235a4d1263
-- title:
--   Is PD: mul
-- statement:
--   The Is PD construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L708-L713
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L708-L713

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

theorem Formalism.GM.GammaExpansion.IsPD.mul {N0 d d' : ℕ} {g g' : ℕ → k} (h : IsPD N0 d g) (h' : IsPD N0 d' g') :
    IsPD N0 (d + d') (fun n => g n * g' n) := by sorry

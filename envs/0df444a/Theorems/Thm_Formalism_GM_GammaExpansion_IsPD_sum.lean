-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_IsPD_sum
-- name    : Formalism.GM.GammaExpansion.IsPD.sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:49:49.014812+00:00
-- url     : https://prove2.me/theorems/84563a28-428e-4c8a-ae22-fec0d2375553
-- title:
--   Is PD: sum
-- statement:
--   The Is PD construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L715-L723
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L715-L723

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

theorem Formalism.GM.GammaExpansion.IsPD.sum {ι : Type} (t : Finset ι) {N0 d : ℕ} (g : ι → ℕ → k) (h : ∀ i ∈ t, IsPD N0 d (g i)) :
    IsPD N0 d (fun n => ∑ i ∈ t, g i n) := by sorry

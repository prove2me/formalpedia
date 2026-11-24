-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_coef_nat
-- name    : Formalism.GM.GammaExpansion.coef_nat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:12.877812+00:00
-- url     : https://prove2.me/theorems/ed208671-efd3-4a4c-b482-76b0ba893923
-- title:
--   Gamma Expansion: coef nat
-- statement:
--   The Gamma Expansion construction uses the coef nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L778-L788
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L778-L788

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
open Finset
variable {k : Type} [Field k] [CharZero k]

theorem Formalism.GM.GammaExpansion.coef_nat (A o s j : ℕ) (hsj : s + j ≤ o) :
    A.choose o * o.factorial =
      (A - s - j).choose (o - s - j) * (o - s - j).factorial * ((A - s).choose j * j.factorial) *
        A.descFactorial s := by sorry

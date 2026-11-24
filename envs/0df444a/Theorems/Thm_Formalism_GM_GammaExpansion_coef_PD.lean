-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_coef_PD
-- name    : Formalism.GM.GammaExpansion.coef_PD
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:14.15826+00:00
-- url     : https://prove2.me/theorems/00d75ae6-cc32-48e6-b3fb-7375ccbc1b75
-- title:
--   Gamma Expansion: coef PD
-- statement:
--   The Gamma Expansion construction uses the coef PD property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L790-L827
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L790-L827

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

theorem Formalism.GM.GammaExpansion.coef_PD (o r z s j S : ℕ) (hr : 1 ≤ r) (hsj : s + j ≤ o) (hoS : o ≤ S) :
    IsPD S (o - s - j) (fun n => (((o + n + r + z - 1).choose o : ℕ) : k) *
      (∏ i ∈ range s, (((z : k) + 1 + i) / ((o + n + r + z - 1 - i : ℕ) : k))) *
        cph k ((o - s) + (n - s) + r + (z + s) - 1) j) := by sorry

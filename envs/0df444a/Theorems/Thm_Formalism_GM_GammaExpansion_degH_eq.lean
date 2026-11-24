-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_degH_eq
-- name    : Formalism.GM.GammaExpansion.degH_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:41.592215+00:00
-- url     : https://prove2.me/theorems/1953e499-ebc1-41f3-b4c7-bb73253f4461
-- title:
--   Gamma Expansion: deg H eq
-- statement:
--   The Gamma Expansion construction uses the deg H eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L968-L975
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L968-L975

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
open MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}

theorem Formalism.GM.GammaExpansion.degH_eq (LL : M.Letters (N + 1)) (e : ℕ) (he : e ≤ LL.deg (Fin.last N)) :
    ∑ b, ((fun b' : Fin (N + 1 + 1) => if b' = Fin.last (N + 1) then 1 else 0) (Fin.castSucc b) +
      (fun b' : Fin (N + 1 + 1) => if b' = Fin.last (N + 1) then 1 else 0) (Fin.last (N + 1))) *
        (lowerLast LL e).deg b = LL.total - e := by sorry

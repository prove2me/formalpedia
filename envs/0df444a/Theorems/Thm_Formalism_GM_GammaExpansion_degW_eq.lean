-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_degW_eq
-- name    : Formalism.GM.GammaExpansion.degW_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:18.339797+00:00
-- url     : https://prove2.me/theorems/975e2936-e730-4e5f-9d2b-458dcc8ce4a5
-- title:
--   Gamma Expansion: deg W eq
-- statement:
--   The Gamma Expansion construction uses the deg W eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L961-L966
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L961-L966

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

theorem Formalism.GM.GammaExpansion.degW_eq (LL : M.Letters (N + 1)) (e : ℕ) :
    ∑ b, ((fun b' : Fin (N + 1 + 1) => if b' = Fin.castSucc (Fin.last N) then 1 else 0) (Fin.castSucc b) +
      (fun b' : Fin (N + 1 + 1) => if b' = Fin.castSucc (Fin.last N) then 1 else 0) (Fin.last (N + 1))) *
        (lowerLast LL e).deg b = LL.deg (Fin.last N) - e := by sorry

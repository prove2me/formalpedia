-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_lowerLast_total
-- name    : Formalism.GM.GammaExpansion.lowerLast_total
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:26.240861+00:00
-- url     : https://prove2.me/theorems/b2479fb1-15aa-4f66-a330-4c200b6cd170
-- title:
--   Gamma Expansion: lower Last total
-- statement:
--   The Gamma Expansion construction uses the lower Last total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L866-L869
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L866-L869

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

theorem Formalism.GM.GammaExpansion.lowerLast_total (LL : M.Letters (N + 1)) (e : ℕ) (he : e ≤ LL.deg (Fin.last N)) :
    (lowerLast LL e).total = LL.total - e := by sorry

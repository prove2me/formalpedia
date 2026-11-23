-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_weight_ind
-- name    : Formalism.GM.GammaExpansion.weight_ind
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:39.502007+00:00
-- url     : https://prove2.me/theorems/00ab09d7-8518-4477-9cc0-2c432326d073
-- title:
--   Gamma Expansion: weight ind
-- statement:
--   The Gamma Expansion construction uses the weight ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L905-L909
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L905-L909

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

theorem Formalism.GM.GammaExpansion.weight_ind {K : ℕ} (b0 : Fin K) (m : Fin K × Fin r →₀ ℕ) :
    Finsupp.weight (fun x : Fin K × Fin r => (if x.1 = b0 then 1 else 0)) m = ∑ c, m (b0, c) := by sorry

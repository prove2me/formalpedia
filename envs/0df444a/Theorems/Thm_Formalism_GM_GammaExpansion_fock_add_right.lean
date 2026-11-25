-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_fock_add_right
-- name    : Formalism.GM.GammaExpansion.fock_add_right
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:45:23.765054+00:00
-- url     : https://prove2.me/theorems/a45bec00-cab2-4cc8-a11c-5c5a16621655
-- title:
--   Gamma Expansion: fock add right
-- statement:
--   The Gamma Expansion construction uses the fock add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L153-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L153-L155

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
variable (p : ℕ) [Fact p.Prime] {σ : Type} [Fintype σ] [DecidableEq σ]

theorem Formalism.GM.GammaExpansion.fock_add_right (F G G' : MvPolynomial σ ℚ_[p]) :
    M.fock p F (G + G') = M.fock p F G + M.fock p F G' := by sorry

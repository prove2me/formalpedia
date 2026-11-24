-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_fw_add_single
-- name    : Formalism.GM.GammaExpansion.fw_add_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:47.354558+00:00
-- url     : https://prove2.me/theorems/091646dd-e854-49b3-a5b7-52ef7fc910f9
-- title:
--   Gamma Expansion: fw add single
-- statement:
--   The Gamma Expansion construction uses the fw add single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L99-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L99-L111

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

theorem Formalism.GM.GammaExpansion.fw_add_single (m : σ →₀ ℕ) (v : σ) :
    fw p (m + Finsupp.single v 1) = fw p m * ((m v + 1 : ℕ) : ℚ_[p]) := by sorry

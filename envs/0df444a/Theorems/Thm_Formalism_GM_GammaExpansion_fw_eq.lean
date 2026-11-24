-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_fw_eq
-- name    : Formalism.GM.GammaExpansion.fw_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:25.052814+00:00
-- url     : https://prove2.me/theorems/96dabfe1-cefd-4d94-94db-07bb4f5ae6ea
-- title:
--   Gamma Expansion: fw eq
-- statement:
--   The Gamma Expansion construction uses the fw eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L96-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L96-L97

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

theorem Formalism.GM.GammaExpansion.fw_eq (m : σ →₀ ℕ) : fw p m = ∏ x, ((m x).factorial : ℚ_[p]) := by sorry

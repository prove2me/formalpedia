-- Prove2me | Theorems.Thm_Formalism_DimensionVariation_fineToUniform6
-- name    : Formalism.DimensionVariation.fineToUniform6
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:25:59.75548+00:00
-- url     : https://prove2.me/theorems/7550fff4-d6c1-4a17-8af5-10330a8dbb4e
-- title:
--   Dimension Variation: fine To Uniform6
-- statement:
--   The Dimension Variation construction uses the fine To Uniform6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/DivIneqRecordTwoConst6.lean#L142-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/DivIneqRecordTwoConst6.lean#L142-L152

import Definitions.Def_Formalism_ThetaSupremumBounds_LiftOperatorBoundOfFockJet
import Definitions.Def_Formalism_ThetaSupremumBounds_FinalJ
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GlobalBoundRefinements
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqRecordTwoConst6
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)

theorem Formalism.DimensionVariation.fineToUniform6 (x eps B0 Nc m c' : ℝ) (hx : 1 ≤ x) (hB : 0 ≤ B0) (hN : 0 ≤ Nc) (hm : 0 ≤ m)
    (h1 : c' ≤ x ^ eps) (h2 : c' * Real.log x ^ 2 ≤ x ^ (2 * eps)) :
    c' * (m * (x ^ eps * B0 + Real.log x ^ 2 * Nc)) ≤ m * (B0 + Nc) * x ^ (2 * eps) := by sorry

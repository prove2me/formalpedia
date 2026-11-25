-- Prove2me | Theorems.Thm_Formalism_DimensionVariation_logPrimeBound6
-- name    : Formalism.DimensionVariation.logPrimeBound6
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:27:53.554069+00:00
-- url     : https://prove2.me/theorems/47283599-2585-4b74-b945-c22f9f787adf
-- title:
--   Dimension Variation: log Prime Bound6
-- statement:
--   The Dimension Variation construction uses the log Prime Bound6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/DivIneqRecordTwoConst6.lean#L154-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaSupremumBounds/DivIneqRecordTwoConst6.lean#L154-L169

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

theorem Formalism.DimensionVariation.logPrimeBound6 (x L b a rd La g nV L' Cg : ℝ) (hx : 1 ≤ x) (hb : b = Real.exp L)
    (ha : a = x * b) (hrd : 1 ≤ rd) (hLa : La = Real.log (a * rd)) (hg : 0 < g) (hgl : Real.log g ≤ Cg * L)
    (hn : 0 < nV) (hnl : Real.log nV ≤ L) (hCg : 0 ≤ Cg) (hL' : L' = Real.log (b * rd * g * nV)) :
    L' ≤ (2 + Cg) * La := by sorry

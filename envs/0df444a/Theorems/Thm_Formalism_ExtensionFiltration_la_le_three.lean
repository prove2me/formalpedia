-- Prove2me | Theorems.Thm_Formalism_ExtensionFiltration_la_le_three
-- name    : Formalism.ExtensionFiltration.la_le_three
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:28:46.796019+00:00
-- url     : https://prove2.me/theorems/3bf4344c-52cd-4ed2-93c7-6560c9b9300f
-- title:
--   Extension Filtration: la le three
-- statement:
--   The Extension Filtration construction uses the la le three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/GlobalBoundRefinements.lean#L60-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/GlobalBoundRefinements.lean#L60-L68

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_CovolumeEstimateAnchoredWeights
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeAssemblyHolds
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeFullAssemblyHolds
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeIntoDivisionHolds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_SpanMuMin
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_TwistLower
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_MuMaxMinkowski
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GlobalBoundRefinements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ExtensionFiltration
open Finset Module NumberField

theorem Formalism.ExtensionFiltration.la_le_three (x eps L b a rd La : ℝ) (hx : 1 ≤ x) (hL : L = x ^ eps) (hb : b = Real.exp L)
    (ha : a = x * b) (hrd : 1 ≤ rd) (hrdL : Real.log rd ≤ L) (hlx : Real.log x ≤ L)
    (hLa : La = Real.log (a * rd)) : La ≤ 3 * x ^ eps := by sorry

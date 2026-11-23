-- Prove2me | Theorems.Thm_Formalism_ExtensionFiltration_span_min_slope
-- name    : Formalism.ExtensionFiltration.span_min_slope
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:54.110861+00:00
-- url     : https://prove2.me/theorems/2dde1f82-41a3-430c-8976-3a89bb5e16b0
-- title:
--   Extension Filtration: span min slope
-- statement:
--   The Extension Filtration construction uses the span min slope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/SpanMuMin.lean#L146-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/SpanMuMin.lean#L146-L186

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNStep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FinSup
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RatioMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_SpanMuMin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.ExtensionFiltration
open Formalism.HN

theorem Formalism.ExtensionFiltration.span_min_slope : SpanMuMin := by sorry

-- Prove2me | Theorems.Thm_Formalism_TruncatedSeriesCounting_TruncatedSeriesCountingIdentities_DetPolyApp_mem_mainNotions_iff_fromT
-- name    : Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyApp.mem_mainNotions_iff_fromT
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:29:43.551988+00:00
-- url     : https://prove2.me/theorems/88f6c8e5-87f8-4b11-867c-09db1323eea2
-- title:
--   Det Poly App: mem main Notions iff from T
-- statement:
--   The Det Poly App construction uses the mem main Notions iff from T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TruncatedSeriesCounting/TruncatedSeriesProofs/LemmaDetPoly.lean#L288-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TruncatedSeriesCounting/TruncatedSeriesProofs/LemmaDetPoly.lean#L288-L288

import Definitions.Def_Formalism_TruncatedSeriesCounting_LemmaDetPoly
import Definitions.Def_Formalism_TruncatedSeriesCounting_TruncatedSeriesProofs_LemmaDetPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical Polynomial
noncomputable section
open Formalism Formalism.TruncatedSeriesCounting Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyApp
open DetPolyCore
variable {O K Xs : Type*} [CommRing O] [CommRing K] [Algebra O K]

theorem Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyApp.mem_mainNotions_iff_fromT {T : Subalgebra O (Xs → O)} {f : Xs → K} : f ∈ MainNotions T ↔ FromT T f := by sorry

-- Prove2me | Theorems.Thm_Formalism_TruncatedSeriesCounting_TruncatedSeriesCountingIdentities_DetPolyApp_charpolyRev_map
-- name    : Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyApp.charpolyRev_map
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:29:12.529537+00:00
-- url     : https://prove2.me/theorems/a4d56d49-6e44-41b6-b8de-a1b9ae704ff6
-- title:
--   Det Poly App: charpoly Rev map
-- statement:
--   The Det Poly App construction uses the charpoly Rev map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TruncatedSeriesCounting/TruncatedSeriesProofs/LemmaDetPoly.lean#L357-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TruncatedSeriesCounting/TruncatedSeriesProofs/LemmaDetPoly.lean#L357-L363

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
variable {K Xs G : Type*} [CommRing K] [Monoid G] {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyApp.charpolyRev_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (M : Matrix n n A) :
    (Matrix.charpolyRev M).map f = Matrix.charpolyRev (M.map f) := by sorry

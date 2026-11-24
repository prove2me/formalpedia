-- Prove2me | Theorems.Thm_Formalism_TruncatedSeriesCounting_TruncatedSeriesCountingIdentities_DetPolyApp_det_eq_coeff
-- name    : Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyApp.det_eq_coeff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:29:16.985097+00:00
-- url     : https://prove2.me/theorems/e2de361e-9f65-4773-b951-12772ebdbe9c
-- title:
--   Det Poly App: det eq coeff
-- statement:
--   The Det Poly App construction uses the det eq coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TruncatedSeriesCounting/TruncatedSeriesProofs/LemmaDetPoly.lean#L365-L370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TruncatedSeriesCounting/TruncatedSeriesProofs/LemmaDetPoly.lean#L365-L370

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

theorem Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyApp.det_eq_coeff {A : Type*} [CommRing A] (M : Matrix n n A) :
    M.det = (-1) ^ Fintype.card n * (Matrix.charpolyRev M).coeff (Fintype.card n) := by sorry

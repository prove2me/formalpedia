-- Prove2me | Theorems.Thm_Formalism_TruncatedSeriesCounting_TruncatedSeriesCountingIdentities_DetPolyCore_C_mem_polyS
-- name    : Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore.C_mem_polyS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:13:38.580812+00:00
-- url     : https://prove2.me/theorems/666a39a5-ef89-4bae-8e26-819a55e9fa28
-- title:
--   Det Poly Core: C mem poly S
-- statement:
--   The Det Poly Core construction uses the C mem poly S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TruncatedSeriesCounting/TruncatedSeriesProofs/LemmaDetPoly.lean#L35-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TruncatedSeriesCounting/TruncatedSeriesProofs/LemmaDetPoly.lean#L35-L41

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
open Formalism Formalism.TruncatedSeriesCounting Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore
variable {R : Type*} [CommRing R] {G : Type*} [Monoid G] {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore.C_mem_polyS {S : Subring R} {c : R} (hc : c ∈ S) : C c ∈ polyS S := by sorry

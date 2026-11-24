-- Prove2me | Theorems.Thm_Formalism_TruncatedSeriesCounting_TruncatedSeriesCountingIdentities_DetPolyCore_allD
-- name    : Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore.allD
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:29:39.333837+00:00
-- url     : https://prove2.me/theorems/7cbb87a9-f6bb-453c-83e0-1a9c8fb4ff08
-- title:
--   Det Poly Core: all D
-- statement:
--   The Det Poly Core construction uses the all D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TruncatedSeriesCounting/TruncatedSeriesProofs/LemmaDetPoly.lean#L236-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TruncatedSeriesCounting/TruncatedSeriesProofs/LemmaDetPoly.lean#L236-L246

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
variable (N : ℕ)
variable {S : Subring R}

theorem Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore.allD (ρ : G →* Matrix n n R) (hS : ∀ g k, (Matrix.charpolyRev (ρ g)).coeff k ∈ S) :
    ∀ j D, 1 ≤ D → N + 1 ≤ D + j → ∀ l : List (R × ℕ × G), Valid S D l → piN N (F ρ l) ∈ SQ N S := by sorry

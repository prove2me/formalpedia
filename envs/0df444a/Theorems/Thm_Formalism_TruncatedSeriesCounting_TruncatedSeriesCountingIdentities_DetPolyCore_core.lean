-- Prove2me | Theorems.Thm_Formalism_TruncatedSeriesCounting_TruncatedSeriesCountingIdentities_DetPolyCore_core
-- name    : Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore.core
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:32:35.371222+00:00
-- url     : https://prove2.me/theorems/231a18a0-f9c6-464e-97d0-4e391d27409e
-- title:
--   Det Poly Core: core
-- statement:
--   The Det Poly Core construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TruncatedSeriesCounting/TruncatedSeriesProofs/LemmaDetPoly.lean#L250-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TruncatedSeriesCounting/TruncatedSeriesProofs/LemmaDetPoly.lean#L250-L262

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

theorem Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities.DetPolyCore.core {S : Subring R} (ρ : G →* Matrix n n R)
    (hS : ∀ g k, (Matrix.charpolyRev (ρ g)).coeff k ∈ S)
    (l : List (R × ℕ × G)) (hl : ∀ L ∈ l, L.1 ∈ S ∧ 1 ≤ L.2.1) (k : ℕ) : (F ρ l).coeff k ∈ S := by sorry

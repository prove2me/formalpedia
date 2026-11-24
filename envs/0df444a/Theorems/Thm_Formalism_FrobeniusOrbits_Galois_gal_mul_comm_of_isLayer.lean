-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Galois_gal_mul_comm_of_isLayer
-- name    : Formalism.FrobeniusOrbits.Galois.gal_mul_comm_of_isLayer
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:52:37.941596+00:00
-- url     : https://prove2.me/theorems/893ea3fe-39da-4701-a83a-a22ec9adac1b
-- title:
--   Galois: gal mul comm of is Layer
-- statement:
--   The Galois construction uses the gal mul comm of is Layer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Galois.lean#L117-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Galois.lean#L117-L121

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Galois
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem Formalism.FrobeniusOrbits.Galois.gal_mul_comm_of_isLayer (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (σ τ : Gal(L/ℚ)) :
    σ * τ = τ * σ := by sorry

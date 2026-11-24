-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Galois_mem_fixedField_zpowers
-- name    : Formalism.FrobeniusOrbits.Galois.mem_fixedField_zpowers
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:52:47.146368+00:00
-- url     : https://prove2.me/theorems/8a63c530-c4e4-4976-83f5-a64f2b6e67c4
-- title:
--   Galois: mem fixed Field zpowers
-- statement:
--   The Galois construction uses the mem fixed Field zpowers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Galois.lean#L195-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Galois.lean#L195-L205

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

theorem Formalism.FrobeniusOrbits.Galois.mem_fixedField_zpowers (τ : Gal(L/ℚ)) (x : L) :
    x ∈ fixedField (Subgroup.zpowers τ) ↔ τ x = x := by sorry

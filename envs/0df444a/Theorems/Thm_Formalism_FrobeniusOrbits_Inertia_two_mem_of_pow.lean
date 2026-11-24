-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Inertia_two_mem_of_pow
-- name    : Formalism.FrobeniusOrbits.Inertia.two_mem_of_pow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:12:10.707913+00:00
-- url     : https://prove2.me/theorems/00e201e7-4534-4eba-ae06-6f8620d6286c
-- title:
--   Inertia: two mem of pow
-- statement:
--   The Inertia construction uses the two mem of pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Inertia.lean#L17-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Inertia.lean#L17-L40

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois
open Formalism.FrobeniusOrbits.Inertia

theorem Formalism.FrobeniusOrbits.Inertia.two_mem_of_pow {R : Type*} [CommRing R] [IsDomain R] (Q : Ideal R) :
    ∀ (i : ℕ) (η : R), η ^ (2 ^ i) = 1 → η ≠ 1 → η - 1 ∈ Q → (2 : R) ∈ Q := by sorry

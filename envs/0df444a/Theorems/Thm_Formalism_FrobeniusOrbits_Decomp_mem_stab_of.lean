-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_mem_stab_of
-- name    : Formalism.FrobeniusOrbits.Decomp.mem_stab_of
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:10:37.505314+00:00
-- url     : https://prove2.me/theorems/0f90aff0-ce43-4d6c-aacd-8442443d08d7
-- title:
--   Decomp: mem stab of
-- statement:
--   The Decomp construction uses the mem stab of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Decomp.lean#L98-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Decomp.lean#L98-L102

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois
open Formalism.FrobeniusOrbits.Decomp

theorem Formalism.FrobeniusOrbits.Decomp.mem_stab_of {G S : Type*} [Group G] [CommRing S] [MulSemiringAction G S] (g : G)
    (I : Ideal S) (h : ∀ z : S, g • z ∈ I ↔ z ∈ I) : g ∈ MulAction.stabilizer G I := by sorry

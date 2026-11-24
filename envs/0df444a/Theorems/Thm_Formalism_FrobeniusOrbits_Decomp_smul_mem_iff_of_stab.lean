-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_smul_mem_iff_of_stab
-- name    : Formalism.FrobeniusOrbits.Decomp.smul_mem_iff_of_stab
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:10:40.300906+00:00
-- url     : https://prove2.me/theorems/796314d6-900e-43b8-b7ac-f7cef06625dc
-- title:
--   Decomp: smul mem iff of stab
-- statement:
--   The Decomp construction uses the smul mem iff of stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Decomp.lean#L104-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Decomp.lean#L104-L108

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

theorem Formalism.FrobeniusOrbits.Decomp.smul_mem_iff_of_stab {G S : Type*} [Group G] [CommRing S] [MulSemiringAction G S]
    (g : G) (I : Ideal S) (hg : g ∈ MulAction.stabilizer G I) (z : S) : g • z ∈ I ↔ z ∈ I := by sorry

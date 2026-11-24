-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Frob_frob_mul_inertia
-- name    : Formalism.FrobeniusOrbits.Frob.frob_mul_inertia
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:52:49.155824+00:00
-- url     : https://prove2.me/theorems/c5120af3-7a73-4a4e-aca9-cd34f6276585
-- title:
--   Frob: frob mul inertia
-- statement:
--   The Frob construction uses the frob mul inertia property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/FrobMulInertia.lean#L15-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/FrobMulInertia.lean#L15-L24

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
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
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Frob

theorem Formalism.FrobeniusOrbits.Frob.frob_mul_inertia {S : Type*} [CommRing S] {G : Type*} [Group G] [MulSemiringAction G S]
    [SMulCommClass G ℤ S] (Q : Ideal S) (ρ τ : G) (hρ : ρ ∈ Q.inertia G)
    (hτ : IsArithFrobAt ℤ τ Q) : IsArithFrobAt ℤ (ρ * τ) Q := by sorry

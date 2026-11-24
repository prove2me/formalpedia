-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_frob_pow_mk
-- name    : Formalism.FrobeniusOrbits.Decomp.frob_pow_mk
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:11:17.775552+00:00
-- url     : https://prove2.me/theorems/a90e9912-47a6-4fff-888e-f514fe59b38b
-- title:
--   Decomp: frob pow mk
-- statement:
--   The Decomp construction uses the frob pow mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Decomp.lean#L18-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Decomp.lean#L18-L31

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

theorem Formalism.FrobeniusOrbits.Decomp.frob_pow_mk {M : Type} [Field M] [NumberField M] (p : ℕ)
    (Q : Ideal (𝓞 M)) [Q.LiesOver (span {(p : ℤ)})] (F : Gal(M/ℚ))
    (hF : IsArithFrobAt ℤ F Q) (k : ℕ) (x : 𝓞 M) :
    Ideal.Quotient.mk Q ((F ^ k) • x) = (Ideal.Quotient.mk Q x) ^ (p ^ k) := by sorry

-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_stab_eq_inertia_mul
-- name    : Formalism.FrobeniusOrbits.Decomp.stab_eq_inertia_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:10:08.884558+00:00
-- url     : https://prove2.me/theorems/06ebc7c4-7fac-412b-abea-70dd4146df31
-- title:
--   Decomp: stab eq inertia mul
-- statement:
--   The Decomp construction uses the stab eq inertia mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Decomp.lean#L89-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Decomp.lean#L89-L96

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

theorem Formalism.FrobeniusOrbits.Decomp.stab_eq_inertia_mul {M : Type} [Field M] [NumberField M] (p : ℕ) [Fact p.Prime]
    (Q : Ideal (𝓞 M)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] (F σ : Gal(M/ℚ))
    (hF : IsArithFrobAt ℤ F Q) (hσ : σ ∈ MulAction.stabilizer Gal(M/ℚ) Q) :
    ∃ k : ℕ, ∃ ρ : Gal(M/ℚ), (∀ x : 𝓞 M, ρ • x - x ∈ Q) ∧ σ = ρ * F ^ k := by sorry

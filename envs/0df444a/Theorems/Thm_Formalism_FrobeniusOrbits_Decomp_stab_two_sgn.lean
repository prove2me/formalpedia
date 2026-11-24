-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Decomp_stab_two_sgn
-- name    : Formalism.FrobeniusOrbits.Decomp.stab_two_sgn
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:11:41.707068+00:00
-- url     : https://prove2.me/theorems/e57fb2ea-af13-462c-9d46-7b556834a8f1
-- title:
--   Decomp: stab two sgn
-- statement:
--   The Decomp construction uses the stab two sgn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Decomp.lean#L321-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Decomp.lean#L321-L389

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
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem Formalism.FrobeniusOrbits.Decomp.stab_two_sgn (hqd : HypOdd q d) (hd16 : d % 16 = 7) (h : IsLayer (e + 2) q d ζ a b)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(2 : ℤ)})]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b)
    (hσ : σ ∈ MulAction.stabilizer (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) P) :
    (galE e ζ a b σ).1.2 = 1 := by sorry

-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Principal_mem_diff_iff
-- name    : Formalism.FrobeniusOrbits.Principal.mem_diff_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:39:31.234528+00:00
-- url     : https://prove2.me/theorems/fad6fe2f-4fd0-4a2c-a6b9-8d5a23a66beb
-- title:
--   Principal: mem diff iff
-- statement:
--   The Principal construction uses the mem diff iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Principal.lean#L166-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Principal.lean#L166-L204

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Inertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Principal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Principal
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
open Formalism.FrobeniusOrbits.Principal
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem Formalism.FrobeniusOrbits.Principal.mem_diff_iff (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (z : 𝓞 (hostE ζ a b)) :
    z ∈ differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) ↔
      ∀ y : (hostE ζ a b), (∀ x : 𝓞 (hostE ζ a b), IsIntegral ℤ (∑ τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b), τ (y * x))) →
        IsIntegral ℤ ((z : (hostE ζ a b)) * y) := by sorry

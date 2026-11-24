-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Principal_comm_symm
-- name    : Formalism.FrobeniusOrbits.Principal.comm_symm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:38:50.163839+00:00
-- url     : https://prove2.me/theorems/9da80281-6269-44e2-bbd5-4fe70bf60b90
-- title:
--   Principal: comm symm
-- statement:
--   The Principal construction uses the comm symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Principal.lean#L112-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/Principal.lean#L112-L116

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

theorem Formalism.FrobeniusOrbits.Principal.comm_symm (σ : (hostE ζ a b) ≃ₐ[ℚ] (hostE ζ a b))
    (hc : ∀ (τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b)) (x : (hostE ζ a b)), σ (τ x) = τ (σ x))
    (τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b)) (x : (hostE ζ a b)) : σ.symm (τ x) = τ (σ.symm x) := by sorry

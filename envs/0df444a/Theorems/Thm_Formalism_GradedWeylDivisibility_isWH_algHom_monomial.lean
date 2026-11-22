-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_isWH_algHom_monomial
-- name    : Formalism.GradedWeylDivisibility.isWH_algHom_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:09:44.353451+00:00
-- url     : https://prove2.me/theorems/410749b6-ce7a-464c-8e05-0538b35b3128
-- title:
--   Graded Weyl Divisibility: is WH alg Hom monomial
-- statement:
--   The Graded Weyl Divisibility construction uses the is WH alg Hom monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LRowstLemmas.lean#L13-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/LRowstLemmas.lean#L13-L26

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowstLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {σ τ M : Type*} [AddCommMonoid M]

theorem Formalism.GradedWeylDivisibility.isWH_algHom_monomial (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R) (w : σ → M) (w' : τ → M)
    (hφ : ∀ v, IsWeightedHomogeneous w' (φ (X v)) (w v)) (m : σ →₀ ℕ) (c : R) :
    IsWeightedHomogeneous w' (φ (monomial m c)) (Finsupp.weight w m) := by sorry

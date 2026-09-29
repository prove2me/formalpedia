-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_isPullback_of_galois_of_finite_action
-- name    : AlgebraicGeometry.Scheme.exists_quotient_isPullback_of_galois_of_finite_action
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/6755ddd5-ae40-5ab1-b3f4-aac06627a054
-- title:
--   Descent of a G-scheme along a Galois extension 𝒪 → 𝒪'
-- statement:
--   Let $\mathcal O$ be a commutative ring and $\mathcal O'$ a commutative $\mathcal O$-algebra which is finite, free and faithfully flat as an $\mathcal O$-module, let $G$ be a finite group and $\tau : G \to \operatorname{Aut}_{\mathcal O\text{-alg}}(\mathcal O')$ a group homomorphism, and assume the Galois condition that the map $\mathcal O' \otimes_{\mathcal O} \mathcal O' \to (G \to \mathcal O')$ sending $x$ to the family indexed by $\sigma \in G$ of the images of $x$ under $\mathrm{id} \otimes \tau_\sigma$ followed by multiplication (so $a \otimes b \mapsto (a\,\tau_\sigma(b))_\sigma$) is bijective. Let $M'$ be a scheme and $\pi_{M'} : M' \to \operatorname{Spec} \mathcal O'$ a morphism which is separated, quasi-compact and locally of finite presentation, such that every finite set of points of $M'$ lies in a single affine open, and such that for some $n$ there is an immersion $\iota : M' \to \mathbf P^n_{\mathcal O'}$ (the $\operatorname{Proj}$ of the graded ring of homogeneous polynomials in $n+1$ variables over $\mathcal O'$) with $\iota$ followed by the structure morphism of $\mathbf P^n_{\mathcal O'}$ equal to $\pi_{M'}$. Let $\rho$ assign to each $\sigma \in G$ a self-isomorphism $\rho_\sigma$ of $M'$ with $\rho_1 = \mathrm{id}_{M'}$, $\rho_{\sigma\sigma'} = \rho_{\sigma'} \circ \rho_\sigma$, and $\pi_{M'} \circ \rho_\sigma = \operatorname{Spec}(\tau_\sigma) \circ \pi_{M'}$. Then there exist a scheme $M$, a morphism $\pi_M : M \to \operatorname{Spec}\mathcal O$ and a morphism $q : M' \to M$ such that $q \circ \rho_\sigma = q$ for all $\sigma$, the square formed by $q$, $\pi_{M'}$, $\pi_M$ and $\operatorname{Spec}$ of $\mathcal O \to \mathcal O'$ is cartesian, and $\pi_M$ is separated, quasi-compact and locally of finite presentation, every finite set of points of $M$ lies in an affine open, and $M$ admits, for some $n$, an immersion into $\mathbf P^n_{\mathcal O}$ over $\operatorname{Spec}\mathcal O$ compatible with $\pi_M$.
--
--   This is the descent step for quotients by a finite group acting over a Galois extension of the base ring: the quotient $M = M'/G$ exists as a quasi-projective $\mathcal O$-scheme and recovers $M'$ after base change to $\mathcal O'$, so that all the finiteness, separatedness and quasi-projectivity properties assumed over $\mathcal O'$ hold over $\mathcal O$. It is used in the construction of fine moduli schemes for polarised abelian schemes, where a moduli space built over a ring containing a root of unity must be descended to the smaller base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_quotient_isPullback_of_galois_of_finite_action.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.Scheme.exists_quotient_isPullback_of_galois_of_finite_action
    (𝒪 : Type) [CommRing 𝒪] (𝒪' : Type) [CommRing 𝒪'] [Algebra 𝒪 𝒪'] [Module.Finite 𝒪 𝒪'] [Module.Free 𝒪 𝒪']
    [Module.FaithfullyFlat 𝒪 𝒪']
    (G : Type) [Group G] [Finite G] (τ : G →* (𝒪' ≃ₐ[𝒪] 𝒪'))
    (hgal : Function.Bijective fun x : 𝒪' ⊗[𝒪] 𝒪' => fun σ : G =>
      Algebra.TensorProduct.lmul' (S := 𝒪') 𝒪
        (Algebra.TensorProduct.map (AlgHom.id 𝒪 𝒪') ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →ₐ[𝒪] 𝒪') x))
    (M' : Scheme.{0}) (πM' : M' ⟶ Spec (CommRingCat.of 𝒪'))
    (hsep : IsSeparated πM') (hqc : QuasiCompact πM') (hfp : LocallyOfFinitePresentation πM')
    (hAF : ∀ F : Finset M', ∃ U : M'.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
    (hQP : ∃ (qpn : ℕ) (qpι : M' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) 𝒪')),
      IsImmersion qpι ∧ qpι ≫ ProjSpace.π 𝒪' qpn = πM')
    (ρ : G → (M' ≅ M')) (hρ1 : (ρ 1).hom = 𝟙 M') (hρmul : ∀ σ σ' : G, (ρ (σ * σ')).hom = (ρ σ).hom ≫ (ρ σ').hom)
    (hρπ : ∀ σ : G, (ρ σ).hom ≫ πM' = πM' ≫ Spec.map (CommRingCat.ofHom ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪'))) :
    ∃ (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of 𝒪)) (q : M' ⟶ M),
      (∀ σ : G, (ρ σ).hom ≫ q = q) ∧
      CategoryTheory.IsPullback q πM' πM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 𝒪'))) ∧
      IsSeparated πM ∧ QuasiCompact πM ∧ LocallyOfFinitePresentation πM ∧
      (∀ F : Finset M, ∃ U : M.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) ∧
      (∃ (qpn : ℕ) (qpι : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) 𝒪)),
        IsImmersion qpι ∧ qpι ≫ ProjSpace.π 𝒪 qpn = πM) := by sorry

-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_ringEquiv_tensor_sections_baseChange_inter
-- name    : AlgebraicGeometry.Scheme.OrderedAffineCover.exists_ringEquiv_tensor_sections_baseChange_inter
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/adc62165-3c26-58a9-9c77-305b6d1f1bb0
-- title:
--   Sections over a base-changed affine overlap as a tensor product
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme and $\pi\colon X\to\operatorname{Spec} R$ a separated morphism, let $\mathcal U$ be an ordered affine cover of $X$ (a finite linearly ordered index set $\iota$ together with opens $U_i$, each affine, whose supremum is $\top$), let $A$ be a commutative $R$-algebra, and let $s$ be an index of degree $i$, that is a strictly monotone map $\operatorname{Fin}(i+1)\to\iota$, with associated overlap $U_s=\bigsqcap_j U_{s(j)}$. Write $p$ and $p_2$ for the two projections of $Z=X\times_{\operatorname{Spec} R}\operatorname{Spec} A$, and let $\mathcal U_A$ be the base-changed cover of $Z$, whose $i$-th open is $p^{-1}(U_i)$, so that its overlap at $s$ is $\bigsqcap_j p^{-1}(U_{s(j)})$. Give $\Gamma(X,U_s)$ the $R$-algebra structure coming from $\pi$ and $\Gamma(Z,(\mathcal U_A)_s)$ the $A$-algebra structure coming from $p_2$. The assertion is that there exists a ring isomorphism $\sigma\colon A\otimes_R\Gamma(X,U_s)\to\Gamma(Z,(\mathcal U_A)_s)$ such that $\sigma(1\otimes x)$ is the pullback $p^{*}x$ of $x\in\Gamma(X,U_s)$ restricted along the inclusion $(\mathcal U_A)_s\le p^{-1}(U_s)$, and $\sigma(a\otimes 1)$ is the image of $a$ under the structure map $A\to\Gamma(Z,(\mathcal U_A)_s)$. Note that $\sigma$ is produced as a ring isomorphism only, the two displayed identities recording its compatibility with both structure maps.
--
--   This is the Čech-level input for base change of an ordered affine cover: on each simplex of the cover, the sections of the base-changed scheme are the tensor product of the sections upstairs with $A$. It is used wherever cohomology of a scheme over $R$ is compared with that of its base change to an $R$-algebra $A$, for instance in the computations of deformations and of Picard-type data that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_ringEquiv_tensor_sections_baseChange_inter.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.exists_ringEquiv_tensor_sections_baseChange_inter
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R)) [IsSeparated π]
    (𝒰 : X.OrderedAffineCover) (A : Type u) [CommRing A] [Algebra R A] {i : ℕ} (s : 𝒰.Idx i) :
    letI := algebraOfHom π (𝒰.inter s)
    letI := algebraOfHom (pullback.snd π (specMap R A)) ((𝒰.baseChange π A).inter s)
    ∃ σ : (A ⊗[R] Γ(X, 𝒰.inter s)) ≃+* Γ(pullback π (specMap R A), (𝒰.baseChange π A).inter s),
      (∀ x : Γ(X, 𝒰.inter s),
        σ ((1 : A) ⊗ₜ[R] x) =
          ((pullback π (specMap R A)).presheaf.map (homOfLE (𝒰.baseChange_inter_le π A s)).op).hom
            (((pullback.fst π (specMap R A)).app (𝒰.inter s)).hom x)) ∧
      (∀ a : A, σ (a ⊗ₜ[R] (1 : Γ(X, 𝒰.inter s))) = algebraMap A Γ(pullback π (specMap R A), (𝒰.baseChange π A).inter s) a) := by sorry

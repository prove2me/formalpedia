-- Prove2me | Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_ringHom_apply_eq_of_apply_eq_pullback
-- name    : AlgebraicGeometry.GradedOAlgebra.ringHom_apply_eq_of_apply_eq_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/41f1eb2b-d3fd-5e8b-9f82-6bb3dc451b34
-- title:
--   Uniqueness of a degreewise pull-back-compatible ring map
-- statement:
--   Let $c : X' \to X$ be a morphism of schemes, $L$ a module on $X$ and $L'$ a module on $X'$, and let $e, e'$ be two isomorphisms $c^{*}L \cong L'$ which are assumed equal. Let $S, S'$ be commutative rings, $R$ a commutative $S$-algebra equipped with a family of $S$-submodules $\mathcal{R} : \mathbb{N} \to \mathrm{Submodule}\,S\,R$ making it a graded algebra, and $R'$ a commutative $S'$-algebra equipped with a family of $S'$-submodules $\mathcal{R}'$ (no grading condition on $\mathcal{R}'$ is required). Suppose given maps $\iota_n : \mathcal{R}_n \to \Gamma(L^{\otimes n}, \top)$ and $\iota'_n : \mathcal{R}'_n \to \Gamma(L'^{\otimes n}, \top)$ into the global sections of the tensor powers, where $L^{\otimes 0}$ is the unit module and $L^{\otimes (n+1)} = L^{\otimes n} \otimes L$, with every $\iota'_n$ injective. Let $\vartheta, \vartheta' : R \to R'$ be ring homomorphisms, each carrying $\mathcal{R}_n$ into $\mathcal{R}'_n$ for every $n$, and suppose that for all $n$ and all $x \in \mathcal{R}_n$ the section $\iota'_n(\vartheta x)$ is obtained from $\iota_n(x)$ by applying the unit of the pullback–pushforward adjunction for $c$ at $L^{\otimes n}$ on sections over $\top$, followed by the isomorphism $c^{*}(L^{\otimes n}) \cong (c^{*}L)^{\otimes n}$ coming from monoidality of pullback and then the $n$-th tensor power of $e$, and that the same holds for $\vartheta'$ with $e'$ in place of $e$. Then $\vartheta x = \vartheta' x$ for every $x \in R$.
--
--   This is the uniqueness half of the comparison of graded section rings along a morphism of schemes: a ring map into $R'$ is determined by its effect on homogeneous elements, once these are pinned down by the pull-back formula for sections of tensor powers. It is used in the verification of the cocycle condition for such comparison maps, [`AlgebraicGeometry.GradedOAlgebra.IsSectionRing.cocycle_trans_symm_of_cocycle`](thm.html#AlgebraicGeometry.GradedOAlgebra.IsSectionRing.cocycle_trans_symm_of_cocycle), where two a priori different identifications have to be recognised as giving the same homomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_GradedOAlgebra_ringHom_apply_eq_of_apply_eq_pullback.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

theorem AlgebraicGeometry.GradedOAlgebra.ringHom_apply_eq_of_apply_eq_pullback
    {X X' : Scheme.{u}} (c : X' ⟶ X) (L : X.Modules) (L' : X'.Modules)
    (e e' : (Scheme.Modules.pullback c).obj L ≅ L') (he : e = e')
    {S S' : Type u} [CommRing S] [CommRing S']
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (R' : Type u) [CommRing R'] [Algebra S' R'] (𝓡' : ℕ → Submodule S' R')
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (ι' : ∀ n : ℕ, 𝓡' n → Γ(L'.tensorPow n, ⊤))
    (hι' : ∀ n, Function.Injective (ι' n))
    (ϑ : R →+* R') (hϑdeg : ∀ n, ∀ x ∈ 𝓡 n, ϑ x ∈ 𝓡' n)
    (ϑ' : R →+* R') (hϑ'deg : ∀ n, ∀ x ∈ 𝓡 n, ϑ' x ∈ 𝓡' n)
    (hϑ : ∀ (n : ℕ) (x : 𝓡 n), ι' n ⟨ϑ x, hϑdeg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤) (ι n x)))
    (hϑ' : ∀ (n : ℕ) (x : 𝓡 n), ι' n ⟨ϑ' x, hϑ'deg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e' n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤) (ι n x))) :
    ∀ x : R, ϑ x = ϑ' x := by sorry

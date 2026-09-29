-- Prove2me | Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_isBaseChange_of_apply_eq_pullback_of_flat
-- name    : AlgebraicGeometry.GradedOAlgebra.IsSectionRing.isBaseChange_of_apply_eq_pullback_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/2cc47e7c-f806-52ac-965b-a8ff7b42f90f
-- title:
--   Section rings commute with flat base change
-- statement:
--   Let $S$ be a commutative ring and $S'$ a commutative $S$-algebra which is flat as an $S$-module. Let $f : X \to \operatorname{Spec} S$ be quasi-compact and separated, let $f' : X' \to \operatorname{Spec} S'$, and let $c : X' \to X$ make the square with $f$, $f'$ and $\operatorname{Spec}$ of $S \to S'$ cartesian. Let $L$ be a module on $X$ which is invertible in the sense that every point has an open neighbourhood $U$ with $L|_U$ isomorphic to the unit module of $U$, let $L'$ be a module on $X'$, and let $e : c^{*}L \cong L'$. Let $R$ be a commutative $S$-algebra graded by submodules $\mathcal R_n \subseteq R$, and $\iota_n : \mathcal R_n \to \Gamma(L^{\otimes n}, \top)$ a family making $(R, \mathcal R, \iota)$ a section ring for $f$ and $L$: each $\iota_n$ is bijective and additive, satisfies $\iota_n(s \cdot x) = f^{\#}(s)\,\iota_n(x)$ for the image $f^{\#}(s) \in \Gamma(X, \top)$ of $s \in S$, sends $1 \in \mathcal R_0$ to the unit section, and is multiplicative via the canonical isomorphisms $L^{\otimes m} \otimes L^{\otimes n} \cong L^{\otimes (m+n)}$. Let $(R', \mathcal R', \iota')$ be a section ring for $f'$ and $L'$ over $S'$, with $R'$ also an $S$-algebra compatibly with $S \to S' \to R'$. Let $\theta : R \to R'$ be an $S$-algebra map with $\theta(\mathcal R_n) \subseteq \mathcal R'_n$ such that for all $n$ and $x \in \mathcal R_n$, $\iota'_n(\theta x)$ is the image of $\iota_n(x)$ under the unit of the pullback–pushforward adjunction for $c$ at $L^{\otimes n}$ on $\top$, followed by global sections of $c^{*}(L^{\otimes n}) \cong (c^{*}L)^{\otimes n} \cong L'^{\otimes n}$. Then for every $n$ the $S$-linear map $\mathcal R_n \to \mathcal R'_n$ obtained by restricting $\theta$ exhibits $\mathcal R'_n$ as the base change of $\mathcal R_n$ along $S \to S'$, i.e. the induced $S'$-linear map $S' \otimes_S \mathcal R_n \to \mathcal R'_n$ is an isomorphism.
--
--   This is flat base change for global sections of the powers of an invertible module on a quasi-compact separated $S$-scheme, packaged degreewise for section rings: $S' \otimes_S \Gamma(X, L^{\otimes n}) \cong \Gamma(X', L'^{\otimes n})$. It is the spelling consumed by the constructions of section rings over tensor products of base rings, which invoke it to lift an algebra map to a bijection in each degree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_isBaseChange_of_apply_eq_pullback_of_flat.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

theorem AlgebraicGeometry.GradedOAlgebra.IsSectionRing.isBaseChange_of_apply_eq_pullback_of_flat
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.Flat S S']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) [QuasiCompact f] [IsSeparated f]
    (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (L' : X'.Modules) (e : (Scheme.Modules.pullback c).obj L ≅ L')
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (R' : Type u) [CommRing R'] [Algebra S' R'] [Algebra S R'] [IsScalarTower S S' R']
    (𝓡' : ℕ → Submodule S' R') [GradedAlgebra 𝓡']
    (ι' : ∀ n : ℕ, 𝓡' n → Γ(L'.tensorPow n, ⊤)) (hR' : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f' L' R' 𝓡' ι')
    (θ : R →ₐ[S] R') (hθdeg : ∀ n, ∀ x ∈ 𝓡 n, θ x ∈ 𝓡' n)
    (hθ : ∀ (n : ℕ) (x : 𝓡 n), ι' n ⟨θ x, hθdeg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤) (ι n x)))
    (n : ℕ) :
    IsBaseChange S' ((θ.toLinearMap.restrict (p := 𝓡 n) (q := (𝓡' n).restrictScalars S) (hθdeg n))
      : 𝓡 n →ₗ[S] (𝓡' n).restrictScalars S) := by sorry

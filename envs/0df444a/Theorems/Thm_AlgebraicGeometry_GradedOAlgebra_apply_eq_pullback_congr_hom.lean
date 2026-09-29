-- Prove2me | Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_apply_eq_pullback_congr_hom
-- name    : AlgebraicGeometry.GradedOAlgebra.apply_eq_pullback_congr_hom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/1f2dc44f-8d10-524c-a8dc-e8ddfeeb35bd
-- title:
--   Transport of the pullback comparison formula along c = c'
-- statement:
--   Let $X, X'$ be schemes and let $c, c' : X' \to X$ be morphisms with $h : c = c'$. Let $L$ be a module on $X$, $L'$ a module on $X'$, and $e : c^{*}L \cong L'$ an isomorphism in $X'.\mathrm{Modules}$. Let $S, S'$ be commutative rings, $R$ a commutative $S$-algebra equipped with a family of $S$-submodules $\mathcal R : \mathbb N \to \mathrm{Submodule}\,S\,R$, and likewise $R'$ over $S'$ with $\mathcal R'$ (no compatibility of these families with the multiplications is imposed). Let $\iota_n : \mathcal R_n \to \Gamma(L^{\otimes n}, \top)$ and $\iota'_n : \mathcal R'_n \to \Gamma(L'^{\otimes n}, \top)$ be maps to global sections of the iterated tensor powers $L^{\otimes n}$ defined by $L^{\otimes 0} = \mathbf 1$, $L^{\otimes (n+1)} = L^{\otimes n} \otimes L$, and let $\vartheta : R \to R'$ be a ring homomorphism with $\vartheta(\mathcal R_n) \subseteq \mathcal R'_n$ for all $n$. Assume that for every $n$ and every $x \in \mathcal R_n$ the section $\iota'_n(\vartheta x)$ is obtained from $\iota_n(x)$ by applying the unit of the pullback–pushforward adjunction for $c$ at $L^{\otimes n}$ on $\top$, followed by the global-sections component of the isomorphism $c^{*}(L^{\otimes n}) \cong (c^{*}L)^{\otimes n} \cong L'^{\otimes n}$ built from `Scheme.Modules.pullbackTensorPowIso` for $c$ and the $n$-th tensor power of $e$. The conclusion is the same identity with $c$ replaced throughout by $c'$ and with $e$ replaced by the composite of the inverse of the component at $L$ of `Scheme.Modules.pullbackCongr h` (comparing the pullback functors along $c$ and along $c'$) with $e$.
--
--   This is a bookkeeping transport statement: it says that a degreewise pullback description of a homomorphism of section rings is insensitive to replacing a morphism by a propositionally equal one, the comparison isomorphism being corrected by the canonical identification of the two pullback functors. It is used in the cocycle bookkeeping for section rings, where faces of a Čech-type diagram agree only up to an equality of morphisms, so that comparison maps along them a priori live over syntactically distinct inverse-image functors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_GradedOAlgebra_apply_eq_pullback_congr_hom.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

theorem AlgebraicGeometry.GradedOAlgebra.apply_eq_pullback_congr_hom
    {X X' : Scheme.{u}} (c c' : X' ⟶ X) (h : c = c') (L : X.Modules) (L' : X'.Modules)
    (e : (Scheme.Modules.pullback c).obj L ≅ L')
    {S S' : Type u} [CommRing S] [CommRing S']
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R)
    (R' : Type u) [CommRing R'] [Algebra S' R'] (𝓡' : ℕ → Submodule S' R')
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (ι' : ∀ n : ℕ, 𝓡' n → Γ(L'.tensorPow n, ⊤))
    (ϑ : R →+* R') (hϑdeg : ∀ n, ∀ x ∈ 𝓡 n, ϑ x ∈ 𝓡' n)
    (hϑ : ∀ (n : ℕ) (x : 𝓡 n), ι' n ⟨ϑ x, hϑdeg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤) (ι n x))) :
    ∀ (n : ℕ) (x : 𝓡 n), ι' n ⟨ϑ x, hϑdeg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso c' L n ≪≫ Scheme.Modules.tensorPowMapIso (((Scheme.Modules.pullbackCongr h).app L).symm ≪≫ e) n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction c').unit.app (L.tensorPow n)).app ⊤) (ι n x)) := by sorry

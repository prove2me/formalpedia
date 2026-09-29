-- Prove2me | Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_comp_map_eq_comp
-- name    : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.comp_map_eq_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/a874a13a-139a-5c62-9c97-65abe49c63b3
-- title:
--   Base change of the canonical morphism to Proj
-- statement:
--   Let $S$ be a commutative ring, $S'$ a commutative $S$-algebra, and let $f : X \to \operatorname{Spec} S$, $f' : X' \to \operatorname{Spec} S'$ and $c : X' \to X$ be scheme morphisms such that the square formed by $c$, $f'$, $f$ and $\operatorname{Spec}$ of $S \to S'$ is a pullback. Let $L$ be a module on $X$ that is invertible in the sense that every point has an open neighbourhood $U$ with $L|_U$ isomorphic to the unit sheaf of modules, let $L'$ be a module on $X'$, and let $e : c^{*}L \cong L'$. Let $R$ be a commutative $S$-algebra graded by $S$-submodules $\mathcal R_n$, with maps $\iota_n : \mathcal R_n \to \Gamma(L^{\otimes n}, \top)$ making $(R,\mathcal R,\iota)$ a section ring for $f$ and $L$: each $\iota_n$ is bijective and additive, $\iota_n(s\cdot x) = f^{\sharp}(s)\,\iota_n(x)$ for $s \in S$, $\iota_0(1)$ is the unit section, and $\iota_{m+n}(xy)$ is the image of the tensor product of sections $\iota_m(x)$, $\iota_n(y)$ under $L^{\otimes m} \otimes L^{\otimes n} \cong L^{\otimes (m+n)}$; let $(R',\mathcal R',\iota')$ be such data for $f'$ and $L'$, with $R'$ an $S'$-algebra and an $S$-algebra compatibly. Let $\vartheta : R \to R'$ be an $S$-algebra map with $\vartheta(\mathcal R_n) \subseteq \mathcal R'_n$ such that, for all $n$ and $x \in \mathcal R_n$, $\iota'_n(\vartheta x)$ is the image of $\iota_n(x)$ under the unit of the pullback–pushforward adjunction along $c$ followed by the canonical isomorphisms $c^{*}(L^{\otimes n}) \cong (c^{*}L)^{\otimes n} \cong L'^{\otimes n}$ on global sections, and assume the irrelevant ideal of $\mathcal R'$ lies in the image of the irrelevant ideal of $\mathcal R$ under the induced graded ring map, so that $\operatorname{Proj}(\vartheta) : \operatorname{Proj} \mathcal R' \to \operatorname{Proj} \mathcal R$ is defined. Finally let $\theta : X \to \operatorname{Proj}\mathcal R$ and $\theta' : X' \to \operatorname{Proj}\mathcal R'$ be canonical in the sense of `IsCanonicalToProj`: each is compatible with the structure morphism to the spectrum of the degree-zero part, for $n > 0$ and $\sigma \in \mathcal R_n$ the section $\iota_n(\sigma)$ is a frame on $\theta^{-1}D_+(\sigma)$, and the sections coming from $(R_{(\sigma)})_0$ via $\theta$ satisfy the expected relation $g \cdot \iota_{kn}(\sigma^{k}) = \iota_{kn}(s)$ over $\theta^{-1}D_+(\sigma)$. The conclusion is that $\theta'$ followed by $\operatorname{Proj}(\vartheta)$ equals $c$ followed by $\theta$.
--
--   This is the base-change naturality of the canonical morphism from a scheme carrying an invertible module with section ring to the relative $\operatorname{Proj}$ of that ring: the comparison square over $\operatorname{Spec} S' \to \operatorname{Spec} S$ commutes. It is used in the descent of line bundles along faithfully flat base change, via [`AlgebraicGeometry.exists_descent_of_faithfullyFlat_of_cocycle`](thm.html#AlgebraicGeometry.exists_descent_of_faithfullyFlat_of_cocycle).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_comp_map_eq_comp.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization

theorem AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.comp_map_eq_comp
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (L' : X'.Modules) (e : (Scheme.Modules.pullback c).obj L ≅ L')
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (R' : Type u) [CommRing R'] [Algebra S' R'] [Algebra S R'] [IsScalarTower S S' R']
    (𝓡' : ℕ → Submodule S' R') [GradedAlgebra 𝓡']
    (ι' : ∀ n : ℕ, 𝓡' n → Γ(L'.tensorPow n, ⊤)) (hR' : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f' L' R' 𝓡' ι')
    (ϑ : R →ₐ[S] R') (hϑdeg : ∀ n, ∀ x ∈ 𝓡 n, ϑ x ∈ 𝓡' n)
    (hϑ : ∀ (n : ℕ) (x : 𝓡 n), ι' n ⟨ϑ x, hϑdeg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤) (ι n x)))
    (hirr : HomogeneousIdeal.irrelevant 𝓡' ≤
      (HomogeneousIdeal.irrelevant 𝓡).map ({ ϑ.toRingHom with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡'))
    (θ : X ⟶ Proj 𝓡) (hθ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ)
    (θ' : X' ⟶ Proj 𝓡') (hθ' : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f' L' R' 𝓡' ι' θ') :
    θ' ≫ Proj.map ({ ϑ.toRingHom with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡') hirr = c ≫ θ := by sorry

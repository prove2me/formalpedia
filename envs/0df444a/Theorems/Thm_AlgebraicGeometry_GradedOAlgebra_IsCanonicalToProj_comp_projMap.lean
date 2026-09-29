-- Prove2me | Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_comp_projMap
-- name    : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.comp_projMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/83cecc8b-d0f0-54cb-890a-c3c8d324d8f8
-- title:
--   Composing a canonical morphism to Proj with Proj of a graded map
-- statement:
--   Let $S$ and $S'$ be commutative rings with $S'$ an $S$-algebra, let $X'$ be a scheme, $f' : X' \to \operatorname{Spec} S'$ a morphism and $L'$ an object of $X'.\mathrm{Modules}$. Let $R$ be an $S$-algebra with an $\mathbb{N}$-grading $\mathcal{R}$ by $S$-submodules, and $R'$ an $S'$-algebra which is also an $S$-algebra compatibly (scalar tower $S \to S' \to R'$) with an $\mathbb{N}$-grading $\mathcal{R}'$ by $S'$-submodules. Let $\iota'$ assign to each element of $\mathcal{R}'_n$ a global section of the $n$-th tensor power $L'^{\otimes n}$ (defined recursively, with the unit object in degree $0$), and let $\vartheta : R \to R'$ be an $S$-algebra map carrying $\mathcal{R}_n$ into $\mathcal{R}'_n$ for every $n$, such that the irrelevant ideal of $\mathcal{R}'$ is contained in the image of the irrelevant ideal of $\mathcal{R}$ under the resulting graded ring homomorphism; this last hypothesis is what makes `Proj.map` of that graded homomorphism available. Assume $\theta' : X' \to \operatorname{Proj}\mathcal{R}'$ satisfies `IsCanonicalToProj` for $(f', L', R', \mathcal{R}', \iota')$, i.e. (i) $\theta'$ followed by $\operatorname{Proj}\mathcal{R}' \to \operatorname{Spec}(\mathcal{R}'_0)$ and then by the spectrum of $S' \to R' \to \mathcal{R}'_0$ equals $f'$; (ii) for each $n > 0$ and $\sigma \in \mathcal{R}'_n$, the section $\iota'_n(\sigma)$ is a frame on $\theta'^{-1}D_+(\sigma)$, meaning that on every open $W$ contained in that preimage multiplication by the restriction of $\iota'_n(\sigma)$ is a bijection $\Gamma(X', W) \to \Gamma(L'^{\otimes n}, W)$; (iii) for $n > 0$, $\sigma \in \mathcal{R}'_n$, $k \in \mathbb{N}$ and $s \in \mathcal{R}'_{kn}$, the pullback along $\theta'$ of the function $s/\sigma^k$ on $D_+(\sigma)$ times the restriction of $\iota'_{kn}(\sigma^k)$ equals the restriction of $\iota'_{kn}(s)$. The conclusion is that the same three clauses hold for the data $f'$ followed by $\operatorname{Spec}$ of $S \to S'$, the module $L'$, the graded $S$-algebra $(R, \mathcal{R})$, the section map $n, x \mapsto \iota'_n(\vartheta x)$, and the morphism $\theta'$ followed by `Proj.map` of the graded homomorphism induced by $\vartheta$.
--
--   This is the functoriality in the graded ring of the characterisation of morphisms into $\operatorname{Proj}$ by a line-bundle-like module together with a degreewise family of sections: composing a canonical morphism with $\operatorname{Proj}$ of a degree-preserving algebra map again yields a canonical morphism, for the sections transported along that map and the base changed from $\operatorname{Spec} S'$ to $\operatorname{Spec} S$. It is used by [`AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.comp_map_eq_comp`](thm.html#AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.comp_map_eq_comp) and by [`AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.preimage_basicOpen_comp_projMap_eq`](thm.html#AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.preimage_basicOpen_comp_projMap_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_comp_projMap.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization

theorem AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.comp_projMap
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    {X' : Scheme.{u}} (f' : X' ⟶ Spec (CommRingCat.of S')) (L' : X'.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (R' : Type u) [CommRing R'] [Algebra S' R'] [Algebra S R'] [IsScalarTower S S' R']
    (𝓡' : ℕ → Submodule S' R') [GradedAlgebra 𝓡']
    (ι' : ∀ n : ℕ, 𝓡' n → Γ(L'.tensorPow n, ⊤))
    (ϑ : R →ₐ[S] R') (hϑdeg : ∀ n, ∀ x ∈ 𝓡 n, ϑ x ∈ 𝓡' n)
    (hirr : HomogeneousIdeal.irrelevant 𝓡' ≤
      (HomogeneousIdeal.irrelevant 𝓡).map ({ ϑ.toRingHom with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡'))
    (θ' : X' ⟶ Proj 𝓡') (hθ' : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f' L' R' 𝓡' ι' θ') :
    AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj (f' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S'))) L' R 𝓡
      (fun (n : ℕ) (x : 𝓡 n) => ι' n ⟨ϑ x, hϑdeg n x x.2⟩)
      (θ' ≫ Proj.map ({ ϑ.toRingHom with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡') hirr) := by sorry

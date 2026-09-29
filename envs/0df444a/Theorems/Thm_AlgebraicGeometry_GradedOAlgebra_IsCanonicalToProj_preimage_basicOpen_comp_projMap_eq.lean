-- Prove2me | Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_preimage_basicOpen_comp_projMap_eq
-- name    : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.preimage_basicOpen_comp_projMap_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/e9d62bbc-d90a-5895-a0d9-9bed736afd95
-- title:
--   Base change: equal chart preimages and pulled-back frames
-- statement:
--   Let $S$ and $S'$ be commutative rings with $S'$ an $S$-algebra, let $f : X \to \operatorname{Spec} S$ and $f' : X' \to \operatorname{Spec} S'$ be morphisms of schemes and $c : X' \to X$ a morphism making the square with $f$, $f'$ and $\operatorname{Spec}$ of $S \to S'$ a pullback square; let $L$ be a module on $X$ which is invertible (each point has a neighbourhood $U$ with $L$ pulled back along $U \hookrightarrow X$ isomorphic to the unit sheaf), $L'$ a module on $X'$ and $e : c^{*}L \cong L'$. Let $R$ be an $S$-algebra with an $\mathbb{N}$-grading $\mathcal{R}$ by $S$-submodules and maps $\iota_n : \mathcal{R}_n \to \Gamma(L^{\otimes n}, \top)$ satisfying `IsSectionRing` for $f, L$: each $\iota_n$ is bijective, additive, semilinear for the scalars pulled back from $S$ along $f$, sends $1$ to the unit section and is multiplicative through the isomorphisms $L^{\otimes m} \otimes L^{\otimes n} \cong L^{\otimes(m+n)}$; let $R', \mathcal{R}', \iota'$ be the same data for $f', L'$, with $R'$ an $S'$-algebra and an $S$-algebra compatibly (scalar tower). Let $\vartheta : R \to R'$ be an $S$-algebra map with $\vartheta(\mathcal{R}_n) \subseteq \mathcal{R}'_n$, such that for every $n$ and $x \in \mathcal{R}_n$ the section $\iota'_n(\vartheta x)$ is the image of $\iota_n(x)$ under the unit of the pullback–pushforward adjunction for $c$ followed by the isomorphism $c^{*}(L^{\otimes n}) \cong (c^{*}L)^{\otimes n} \cong L'^{\otimes n}$, and assume the irrelevant ideal of $\mathcal{R}'$ is contained in the image of that of $\mathcal{R}$ under the induced graded ring map. Finally let $\theta : X \to \operatorname{Proj} \mathcal{R}$ and $\theta' : X' \to \operatorname{Proj} \mathcal{R}'$ satisfy `IsCanonicalToProj` for their respective data (compatibility with the structure map to the spectrum of the degree-zero part, the frame property of $\iota_n(\sigma)$ on $\theta^{-1}D_+(\sigma)$ for $n>0$, and the identity relating restrictions of $\iota_{kn}$ to the sections $\operatorname{Proj}$-coming from the homogeneous localisation away from $\sigma$). Then for every $n > 0$ and every $\sigma \in \mathcal{R}_n$: first, the preimage of the basic open $D_+(\sigma)$ of $\operatorname{Proj} \mathcal{R}$ under $\theta'$ followed by $\operatorname{Proj}$ of the graded map induced by $\vartheta$ equals its preimage under $c$ followed by $\theta$; and second, for every $k$, the section of $L'^{\otimes(k \cdot n)}$ obtained by transporting $\iota_{k \cdot n}(\sigma^{k})$ along $c$ by the same adjunction unit and isomorphisms is a frame on that open, i.e. for every open $W$ contained in it, multiplication by functions on $W$ against the restricted section is a bijection from $\Gamma(X', W)$ onto $\Gamma(L'^{\otimes(k \cdot n)}, W)$.
--
--   This is the frame-level content of the naturality of the canonical morphism to $\operatorname{Proj}$ of a section ring under base change: the two candidate morphisms $X' \to \operatorname{Proj} \mathcal{R}$ have the same chart preimages, and the pulled-back powers of $\sigma$ frame the relevant tensor powers there. It supplies exactly the two hypotheses needed by the uniqueness criterion used in [`AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.comp_map_eq_comp`](thm.html#AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.comp_map_eq_comp), which identifies $\theta'$ followed by $\operatorname{Proj}$ of $\vartheta$ with $c$ followed by $\theta$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_preimage_basicOpen_comp_projMap_eq.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization

theorem AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.preimage_basicOpen_comp_projMap_eq
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
    ∀ (n : ℕ), 0 < n → ∀ σ : 𝓡 n,
      (θ' ≫ Proj.map ({ ϑ.toRingHom with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡') hirr) ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) =
          (c ≫ θ) ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) ∧
      ∀ (k : ℕ),
        Scheme.Modules.IsFrameOn
          (((Scheme.Modules.pullbackTensorPowIso c L (k • n) ≪≫ Scheme.Modules.tensorPowMapIso e (k • n)).hom.app ⊤)
            ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow (k • n))).app ⊤)
              (ι (k • n) ⟨(σ : R) ^ k, SetLike.pow_mem_graded k σ.2⟩)))
          ((θ' ≫ Proj.map ({ ϑ.toRingHom with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡') hirr) ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)) := by sorry

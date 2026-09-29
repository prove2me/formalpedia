-- Prove2me | Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_eq_of_preimage_basicOpen_eq
-- name    : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.eq_of_preimage_basicOpen_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/ffe3e971-095e-5456-bcd5-c7e00b7d697f
-- title:
--   Uniqueness of canonical morphisms to Proj from chart preimages
-- statement:
--   Fix a commutative ring $S$, a scheme $X$, a morphism $f \colon X \to \operatorname{Spec} S$, an object $L$ of `X.Modules`, and a commutative $S$-algebra $R$ graded by a family $\mathcal{R} \colon \mathbb{N} \to$ `Submodule S R` making $R$ a graded algebra, together with maps $\iota_n \colon \mathcal{R}_n \to \Gamma(L^{\otimes n}, \top)$ for each $n$, where $L^{\otimes n}$ is the tensor power defined by $L^{\otimes 0} = \mathbf{1}$ and $L^{\otimes(n+1)} = L^{\otimes n} \otimes L$. Let $\theta_1, \theta_2 \colon X \to \operatorname{Proj} \mathcal{R}$ both satisfy `IsCanonicalToProj` for the data $(f, L, R, \mathcal{R}, \iota)$, that is: $\theta_i$ followed by `Proj.toSpecZero` and by `Spec.map` of the composite of the degree-zero projection `GradedRing.projZeroRingHom' 𝓡` with `algebraMap S R` equals $f$; for every $n > 0$ and $\sigma \in \mathcal{R}_n$ the section $\iota_n(\sigma)$ is a frame on $\theta_i^{-1} D_+(\sigma)$, i.e. for every open $W$ contained in $\theta_i^{-1} D_+(\sigma)$ the map $g \mapsto g \cdot (\iota_n(\sigma))|_W$ from $\Gamma(X, W)$ to $\Gamma(L^{\otimes n}, W)$ is bijective; and for all $n > 0$, $\sigma \in \mathcal{R}_n$, $k \in \mathbb{N}$ and $s \in \mathcal{R}_{kn}$, the function $\theta_i^{\sharp}$ applied to the section of $D_+(\sigma)$ determined by $s/\sigma^k$ multiplies $(\iota_{kn}(\sigma^k))|_{\theta_i^{-1}D_+(\sigma)}$ into $(\iota_{kn}(s))|_{\theta_i^{-1}D_+(\sigma)}$. Assume further that $\theta_1^{-1} D_+(\sigma) = \theta_2^{-1} D_+(\sigma)$ for all $n > 0$ and $\sigma \in \mathcal{R}_n$, and that for all such $\sigma$ and all $k \in \mathbb{N}$ the section $\iota_{kn}(\sigma^k)$ is a frame on $\theta_1^{-1} D_+(\sigma)$. Then $\theta_1 = \theta_2$.
--
--   This is the uniqueness half of the universal property of $\operatorname{Proj}$ for a graded algebra together with a line-bundle-like module and degreewise section maps: a morphism to $\operatorname{Proj} \mathcal{R}$ compatible with $f$ and with the $\iota_n$ is determined by its chart preimages, once the powers $\iota_{kn}(\sigma^k)$ are frames there. It is used in the comparison [`AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.comp_map_eq_comp`](thm.html#AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.comp_map_eq_comp) of canonical morphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_eq_of_preimage_basicOpen_eq.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization

theorem AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.eq_of_preimage_basicOpen_eq
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤))
    (θ₁ θ₂ : X ⟶ Proj 𝓡)
    (h₁ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ₁)
    (h₂ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ₂)
    (hpre : ∀ (n : ℕ), 0 < n → ∀ σ : 𝓡 n,
      θ₁ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) = θ₂ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R))
    (hpow : ∀ (n : ℕ), 0 < n → ∀ (σ : 𝓡 n) (k : ℕ),
      Scheme.Modules.IsFrameOn (ι (k • n) ⟨(σ : R) ^ k, SetLike.pow_mem_graded k σ.2⟩) (θ₁ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R))) :
    θ₁ = θ₂ := by sorry

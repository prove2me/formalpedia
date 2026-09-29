-- Prove2me | Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_smul_map_pow_eq_map_of_section
-- name    : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.exists_smul_map_pow_eq_map_of_section
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/5e14f239-8162-5f5a-ad49-e83803c212fa
-- title:
--   Functions on X_σ are ratios t/σ^k
-- statement:
--   Let $S$ be a commutative ring, $X$ a scheme, $f : X \to \operatorname{Spec} S$ a morphism, $L$ a module on $X$, and let $R$ be a commutative $S$-algebra with an $\mathbb N$-graded decomposition by $S$-submodules $\mathcal R_n$, together with maps $\iota_n : \mathcal R_n \to \Gamma(L^{\otimes n}, \top)$, where $L^{\otimes n}$ is formed by `tensorPow`. Assume `IsSectionRing`: each $\iota_n$ is bijective and additive, $\iota_n(s \cdot x) = \mathrm{baseScalar}(f,s) \cdot \iota_n(x)$ for $s \in S$, $\iota_0(1)$ is the unit global section, and $\iota_{m+n}(xy)$ is the image of the tensor product of sections $\iota_m(x) \otimes \iota_n(y)$ under the canonical isomorphism $L^{\otimes m} \otimes L^{\otimes n} \cong L^{\otimes(m+n)}$. Assume further that $L$ is invertible (every point of $X$ has a neighbourhood $U$ on which the restriction of $L$ along $U \hookrightarrow X$ is isomorphic to the unit module), and that `ClosedImmersionBySections` holds for $L$ and $f$: there are $N$ and a `ProjPresentation` of $L$ over $f$ by $N+1$ global sections whose associated morphism to $\operatorname{Proj}$ of the graded polynomial ring in $N+1$ variables over $S$ is a closed immersion. Let $\theta : X \to \operatorname{Proj} \mathcal R_\bullet$ satisfy `IsCanonicalToProj`: composing $\theta$ with the structural morphism to $\operatorname{Spec}$ of the degree-zero part recovers $f$; for each $n > 0$ and $\sigma \in \mathcal R_n$ the section $\iota_n(\sigma)$ is a frame on $X_\sigma := \theta^{-1}D_+(\sigma)$, i.e. multiplication by functions is bijective onto sections of $L^{\otimes n}$ over every open subset of $X_\sigma$; and for all $k$ and $s \in \mathcal R_{kn}$, the pullback along $\theta$ of the section of $\operatorname{Proj}$ attached to $s/\sigma^k$ times $\iota_{kn}(\sigma^k)|_{X_\sigma}$ equals $\iota_{kn}(s)|_{X_\sigma}$. Then for every $n > 0$, every $\sigma \in \mathcal R_n$ and every $g \in \Gamma(X_\sigma, \mathcal O_X)$ there exist $k \in \mathbb N$ and $t \in \mathcal R_{kn}$ with $g \cdot \iota_{kn}(\sigma^k)|_{X_\sigma} = \iota_{kn}(t)|_{X_\sigma}$ in $\Gamma(L^{\otimes kn}, X_\sigma)$.
--
--   This is the surjectivity half of the comparison between the degree-zero part of the localisation $R_{(\sigma)}$ and the ring of functions on the chart $X_\sigma = \theta^{-1}D_+(\sigma)$: every function on the chart is a ratio $t/\sigma^k$ of elements of the section ring. It feeds the proof that the canonical morphism $\theta$ to $\operatorname{Proj}$ is an isomorphism, both in the statement over affine basic opens and in the global form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_smul_map_pow_eq_map_of_section.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization

theorem AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.exists_smul_map_pow_eq_map_of_section
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (hL : Scheme.Modules.IsInvertible L) (hva : Scheme.Modules.ClosedImmersionBySections L f)
    (θ : X ⟶ Proj 𝓡) (hθ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ)
    (n : ℕ) (hn : 0 < n) (σ : 𝓡 n) (g : Γ(X, θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R))) :
    ∃ (k : ℕ) (t : 𝓡 (k • n)),
      g • (L.tensorPow (k • n)).presheaf.map (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) ≤ ⊤)).op
          (ι (k • n) ⟨(σ : R) ^ k, SetLike.pow_mem_graded k σ.2⟩) =
        (L.tensorPow (k • n)).presheaf.map (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) ≤ ⊤)).op (ι (k • n) t) := by sorry

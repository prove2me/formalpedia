-- Prove2me | Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_pow_mul_eq_zero_of_map_eq_zero
-- name    : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.exists_pow_mul_eq_zero_of_map_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/7ef2b4b2-5ff6-55f9-922f-f0083e4ccc68
-- title:
--   Sections vanishing on X_σ are σ-torsion
-- statement:
--   Let $S$ be a commutative ring, $X$ a scheme with a morphism $f : X \to \operatorname{Spec} S$, and $L$ an object of `X.Modules`. Let $R$ be a commutative $S$-algebra graded by $S$-submodules $\mathcal R_n$, $n \in \mathbb N$, and let maps $\iota_n : \mathcal R_n \to \Gamma(L^{\otimes n}, \top)$ be given, where $L^{\otimes n}$ is the iterated tensor power `L.tensorPow n`. Assume `IsSectionRing`: each $\iota_n$ is bijective and additive, $\iota_n(s \cdot x) = \mathrm{baseScalar}(f)(s)\,\iota_n(x)$ for $s \in S$, $\iota_0(1)$ is the unit global section of $\mathbf 1_{X\text{-Mod}}$, and $\iota_{m+n}(xy)$ is the image of the tensor product of sections $\iota_m(x)$ and $\iota_n(y)$ under the canonical isomorphism $L^{\otimes m} \otimes L^{\otimes n} \cong L^{\otimes (m+n)}$. Assume further that $L$ is invertible (every point of $X$ has an open neighbourhood $U$ on which the pullback of $L$ along $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules), and that `ClosedImmersionBySections L f` holds, i.e. for some $N$ there is a `ProjPresentation` of $L$ over $f$ by global sections $\sigma_0,\dots,\sigma_N$ whose associated morphism $X \to \operatorname{Proj}$ of the homogeneous submodules of $S[X_0,\dots,X_N]$ is a closed immersion. Finally let $\theta : X \to \operatorname{Proj} \mathcal R$ satisfy `IsCanonicalToProj`: $\theta$ followed by $\operatorname{Proj}\mathcal R \to \operatorname{Spec} R_0$ and by the map of spectra induced by $S \to R \to R_0$ equals $f$; for every $n > 0$ and $\sigma \in \mathcal R_n$ the section $\iota_n(\sigma)$ is a frame on $X_\sigma := \theta^{-1}D_+(\sigma)$, meaning that on every open $W \le X_\sigma$ multiplication by sections of $\mathcal O_X$ on the restriction of $\iota_n(\sigma)$ is a bijection onto $\Gamma(L^{\otimes n}, W)$; and for $n>0$, $\sigma \in \mathcal R_n$, $k \in \mathbb N$ and $s \in \mathcal R_{kn}$, the restriction of $\iota_{kn}(s)$ to $X_\sigma$ equals the pullback along $\theta$ of the degree-zero element $s/\sigma^k$ of the homogeneous localisation away from $\sigma$, acting on the restriction of $\iota_{kn}(\sigma^k)$. Then, for $n > 0$, $\sigma \in \mathcal R_n$, $m \in \mathbb N$ and $t \in \mathcal R_m$ whose section $\iota_m(t)$ restricts to $0$ on $X_\sigma$, there exists $k \in \mathbb N$ with $\sigma^k t = 0$ in $R$.
--
--   This is the injectivity half of the classical comparison between the degree-zero part of the homogeneous localisation $R_{(\sigma)}$ and the sections of $L^{\otimes \bullet}$ over the chart $X_\sigma = \theta^{-1}D_+(\sigma)$: a homogeneous element of $R$ whose section dies on the chart is killed by a power of $\sigma$. It is used in the proof that the canonical morphism $\theta : X \to \operatorname{Proj} \mathcal R$ attached to a section ring is an isomorphism, both globally and after restriction to the basic opens over affine opens.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_pow_mul_eq_zero_of_map_eq_zero.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization

theorem AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.exists_pow_mul_eq_zero_of_map_eq_zero
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (hL : Scheme.Modules.IsInvertible L) (hva : Scheme.Modules.ClosedImmersionBySections L f)
    (θ : X ⟶ Proj 𝓡) (hθ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ)
    (n : ℕ) (hn : 0 < n) (σ : 𝓡 n) (m : ℕ) (t : 𝓡 m)
    (ht : (L.tensorPow m).presheaf.map (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) ≤ ⊤)).op (ι m t) = 0) :
    ∃ k : ℕ, (σ : R) ^ k * (t : R) = 0 := by sorry

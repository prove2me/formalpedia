-- Prove2me | Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_pow_eq_zero_of_preimage_basicOpen_eq_bot
-- name    : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.exists_pow_eq_zero_of_preimage_basicOpen_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/762c0e06-ae45-55ef-8a33-45d7a734ed01
-- title:
--   Empty chart forces nilpotence of a homogeneous section
-- statement:
--   Fix a commutative ring $S$, a scheme $X$, a morphism $f : X \to \operatorname{Spec} S$, an object $L$ of $X.\mathrm{Modules}$, and a commutative $S$-algebra $R$ together with an $\mathbb{N}$-grading $\mathcal{R}$ by $S$-submodules making $R$ a graded algebra, and maps $\iota_n : \mathcal{R}_n \to \Gamma(L^{\otimes n}, \top)$ into the global sections of the tensor powers $L^{\otimes n}$ (defined by $L^{\otimes 0} = \mathbf{1}$, $L^{\otimes (n+1)} = L^{\otimes n} \otimes L$). Assume `IsSectionRing`: each $\iota_n$ is bijective and additive, $\iota_n(s \cdot x) = \mathrm{baseScalar}(f)(s) \cdot \iota_n(x)$ for $s \in S$, $\iota_0(1)$ is the unit section, and $\iota_{m+n}(xy)$ is the image of the tensor product of sections $\iota_m(x) \otimes \iota_n(y)$ under the canonical isomorphism $L^{\otimes m} \otimes L^{\otimes n} \cong L^{\otimes(m+n)}$. Assume further that $L$ is invertible, i.e. every point of $X$ has an open neighbourhood $U$ on which the pullback of $L$ along $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules; and that $L$ is a closed immersion by sections over $f$, i.e. for some $N$ there is a projective presentation of $L$ relative to $f$ with $N+1$ sections whose associated morphism to $\mathbf{P}^N_S$ is a closed immersion. Let $\theta : X \to \operatorname{Proj} \mathcal{R}$ satisfy `IsCanonicalToProj` for $f, L, R, \mathcal{R}, \iota$: composing $\theta$ with $\operatorname{Proj}\mathcal{R} \to \operatorname{Spec} \mathcal{R}_0$ and $\operatorname{Spec}$ of $S \to R \to \mathcal{R}_0$ recovers $f$; for every $n > 0$ and $\sigma \in \mathcal{R}_n$ the section $\iota_n(\sigma)$ is a frame on $\theta^{-1}D_+(\sigma)$, meaning that on each open $W$ contained in that preimage the map $g \mapsto g \cdot \iota_n(\sigma)|_W$ from $\Gamma(X, W)$ to $\Gamma(L^{\otimes n}, W)$ is bijective; and for $n > 0$, $\sigma \in \mathcal{R}_n$, $k \in \mathbb{N}$ and $s \in \mathcal{R}_{k \cdot n}$, the $\theta$-pullback of the section of $\operatorname{Proj}\mathcal{R}$ attached to $s/\sigma^k$ on $D_+(\sigma)$ multiplied by the restriction of $\iota_{kn}(\sigma^k)$ equals the restriction of $\iota_{kn}(s)$. Then for $n > 0$ and $\sigma \in \mathcal{R}_n$ such that the open subset $\theta^{-1}D_+(\sigma)$ of $X$ is empty, there exists $k \in \mathbb{N}$ with $\sigma^k = 0$ in $R$.
--
--   This is the nilpotence criterion underlying dominance of the canonical morphism $\theta : X \to \operatorname{Proj}\mathcal{R}$ attached to a section ring: a homogeneous element of positive degree whose basic open chart pulls back to the empty set must be nilpotent, so that every non-empty $D_+(\sigma)$ meets the image of $\theta$. It is used in the proofs that $\theta$ has dense range ([`AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.denseRange`](thm.html#AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.denseRange)) and that $\theta$ is an isomorphism ([`AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.isIso`](thm.html#AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.isIso)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_pow_eq_zero_of_preimage_basicOpen_eq_bot.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization

theorem AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.exists_pow_eq_zero_of_preimage_basicOpen_eq_bot
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (hL : Scheme.Modules.IsInvertible L) (hva : Scheme.Modules.ClosedImmersionBySections L f)
    (θ : X ⟶ Proj 𝓡) (hθ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ)
    (n : ℕ) (hn : 0 < n) (σ : 𝓡 n) (hσ : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) = ⊥) :
    ∃ k : ℕ, (σ : R) ^ k = 0 := by sorry

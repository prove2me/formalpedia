-- Prove2me | Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_universallyClosed
-- name    : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.universallyClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/65e1cc70-3bc6-5f39-aa95-f15f5d4e1d33
-- title:
--   The canonical morphism to Proj is universally closed
-- statement:
--   Let $S$ be a commutative ring, $X$ a scheme, $f : X \to \operatorname{Spec} S$ a morphism and $L$ a sheaf of modules on $X$. Let $R$ be a commutative $S$-algebra with an $\mathbb{N}$-grading given by $S$-submodules $\mathcal{R}_n$, and for each $n$ let $\iota_n : \mathcal{R}_n \to \Gamma(L^{\otimes n}, \top)$ be a map, where $L^{\otimes n}$ is the $n$-fold tensor power (the monoidal unit for $n = 0$). Assume: (i) `IsSectionRing`, i.e. each $\iota_n$ is bijective and additive, $\iota_n(s \cdot x) = (\text{pullback of } s \text{ along } f) \cdot \iota_n(x)$ for $s \in S$, $\iota_0(1)$ is the unit section $1$, and $\iota_{m+n}(xy)$ is the image of the tensor product of sections $\iota_m(x)$, $\iota_n(y)$ under the canonical isomorphism $L^{\otimes m} \otimes L^{\otimes n} \cong L^{\otimes(m+n)}$; (ii) $L$ is invertible, i.e. every point of $X$ has an open neighbourhood $U$ on which the restriction of $L$ is isomorphic to the unit module; (iii) `ClosedImmersionBySections`: there are an $N$ and a projective presentation of $L$ over $f$ — sections $\sigma_0,\dots,\sigma_N \in \Gamma(L,\top)$ together with a morphism $X \to \mathbb{P}^N_S = \operatorname{Proj}$ of the homogeneous submodules of $S[X_0,\dots,X_N]$ lying over $f$, framing $L$ on the preimages of the $D_+(X_i)$ and matching the coordinate ratios — whose morphism to $\mathbb{P}^N_S$ is a closed immersion. Finally let $\theta : X \to \operatorname{Proj}\mathcal{R}$ satisfy `IsCanonicalToProj`: $\theta$ followed by $\operatorname{Proj}\mathcal{R} \to \operatorname{Spec} \mathcal{R}_0 \to \operatorname{Spec} S$ equals $f$; for $n > 0$ and $\sigma \in \mathcal{R}_n$ the section $\iota_n(\sigma)$ is a frame for $L^{\otimes n}$ on $\theta^{-1}D_+(\sigma)$; and on $\theta^{-1}D_+(\sigma)$ the pullback of the degree-zero fraction $s/\sigma^k$ scales $\iota_{kn}(\sigma^k)$ to $\iota_{kn}(s)$ for $s \in \mathcal{R}_{kn}$. Then $\theta$ is universally closed.
--
--   This is the properness half of the comparison of $X$ with the $\operatorname{Proj}$ of its section ring: since $X$ is projective over $S$ by the given presentation and $\operatorname{Proj}\mathcal{R}$ is separated over $S$, the canonical morphism $\theta$ has closed image. It feeds into the proof that $\theta$ is an isomorphism, [`AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.isIso`](thm.html#AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.isIso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_universallyClosed.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization

theorem AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.universallyClosed
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (hL : Scheme.Modules.IsInvertible L) (hva : Scheme.Modules.ClosedImmersionBySections L f)
    (θ : X ⟶ Proj 𝓡) (hθ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ) :
    UniversallyClosed θ := by sorry

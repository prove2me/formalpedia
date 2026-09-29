-- Prove2me | Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_denseRange
-- name    : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.denseRange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/8c30e719-706d-5c56-9974-845b3d9a154a
-- title:
--   The canonical morphism to Proj has dense image
-- statement:
--   Let $S$ be a commutative ring, $X$ a scheme, $f : X \to \operatorname{Spec} S$ a morphism, and $L$ an object of `X.Modules`, with tensor powers $L^{\otimes n}$ formed recursively ($L^{\otimes 0}$ the unit module, $L^{\otimes(n+1)} = L^{\otimes n}\otimes L$). Let $R$ be an $S$-algebra graded by $S$-submodules $\mathcal R_n$, $n \in \mathbb N$, and let $\iota_n : \mathcal R_n \to \Gamma(L^{\otimes n}, \top)$ be maps. Assume `IsSectionRing`: each $\iota_n$ is bijective and additive, $\iota_n(s\cdot x) = f^\sharp(s)\cdot \iota_n(x)$ for the global section $f^\sharp(s)$ attached to $s \in S$, $\iota_0(1)$ is the unit section, and $\iota_{m+n}(xy)$ is the tensor product section $\iota_m(x)\otimes\iota_n(y)$ transported along the canonical isomorphism $L^{\otimes m}\otimes L^{\otimes n}\cong L^{\otimes(m+n)}$. Assume further that $L$ is invertible, i.e. every point of $X$ has a neighbourhood $U$ with $L|_U$ isomorphic to the unit module; and that `ClosedImmersionBySections` holds for $L$ and $f$, i.e. some `ProjPresentation` of $L$ over $f$ by $N+1$ global sections has a morphism to $\operatorname{Proj}$ of the polynomial ring that is a closed immersion. Finally let $\theta : X \to \operatorname{Proj}\mathcal R$ satisfy `IsCanonicalToProj`: $\theta$ followed by the structure morphism to $\operatorname{Spec}$ of the degree-zero part, then $\operatorname{Spec}$ of $S \to R \to R_0$, equals $f$; for each $n > 0$ and $\sigma \in \mathcal R_n$ the section $\iota_n(\sigma)$ is a frame on $\theta^{-1}D_+(\sigma)$ (multiplication by it is bijective on sections over every smaller open); and the pullbacks under $\theta$ of the degree-zero fractions $s/\sigma^k$ rescale $\iota(\sigma^k)$ to $\iota(s)$ for $s \in \mathcal R_{kn}$. Then the range of the underlying continuous map of $\theta$ is dense in $\operatorname{Proj}\mathcal R$.
--
--   This is the density half of the classical statement that, for an invertible sheaf with enough sections, the canonical morphism to the $\operatorname{Proj}$ of its section ring is a closed immersion onto all of $\operatorname{Proj}$. It is used, together with closedness of the image, in [`AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.isIso`](thm.html#AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.isIso) to obtain surjectivity and hence that $\theta$ is an isomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_denseRange.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization

theorem AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.denseRange
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (hL : Scheme.Modules.IsInvertible L) (hva : Scheme.Modules.ClosedImmersionBySections L f)
    (θ : X ⟶ Proj 𝓡) (hθ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ) :
    DenseRange θ.base := by sorry

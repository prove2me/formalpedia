-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.isThetaAdapted_of_isReframe_inter
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/c04aa42d-c511-54de-873a-aea216eff032
-- title:
--   Reframing by an intertwiner preserves theta-adaptedness
-- statement:
--   Fix natural numbers $g$, $N$, $n$ and a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with every $\delta_i$ nonzero and $\prod_i \delta_i = N+1$, together with a bijection $e$ between $\mathrm{Fin}(N+1)$ and $H(\delta) = \prod_i \mathbb{Z}/\delta_i$. Let $B$ be a commutative ring in which $N+1$ is invertible, $\zeta \in B$ with $\zeta^{N+1} = 1$ and $1 - \zeta^{j}$ a unit for $0 < j < N+1$, and $\omega \in B$ with $\omega^{2} = \zeta$. Let $S$ be a commutative ring, $\varphi_B : B \to S$ a ring homomorphism, and $\gamma$ an element of the subgroup $\Gamma$ of automorphisms of the Heisenberg group $\mathrm{Heis}(\delta, N+1)$ fixing every central element $\mathrm{cen}\,a$. Let $X$, $X'$ be framed polarised abelian schemes of type $(g, N, n)$ over $S$, i.e. polarised abelian schemes equipped with a degree-$N$ projective presentation of the polarising module whose associated morphism to projective space is a closed immersion and whose sections $\sigma_0,\dots,\sigma_N$ form a section basis. Let $U = \mathrm{inter}(\gamma^{-1})$ be the chosen $(N+1)\times(N+1)$ intertwiner over $B$ for the Schrödinger representation $z \mapsto \mathrm{schrodMat}(z)$ attached to $\delta$, $N+1$, $\omega$, $e$ (a unit matrix $U$ with $U\,\mathrm{schrodMat}(z) = \mathrm{schrodMat}(\gamma^{-1}z)\,U$ for all $z$, if one exists, and the identity otherwise). Assume that $X'$ is obtained from $X$ by reframing along $\varphi_B(U^{\mathsf T})$: $X'$ has the same underlying polarised abelian scheme as $X$ and a projective presentation whose sections are $\sigma'_i = \sum_j \varphi_B(U^{\mathsf T})_{ij}\,\sigma_j$ (scalars acting through the global sections of the structure morphism), again a closed immersion and a section basis. Assume further that $X$ is theta-adapted for $\delta$ and $e$, meaning that there is a Schrödinger frame for $X$ along the identity of $\operatorname{Spec} S$ whose section indexed by $e(i)$ is the pullback of $\sigma_i$ for every $i$. Then $X'$ is theta-adapted for $\delta$ and $e$ as well.
--
--   This is the invariance of Mumford's theta-adapted frames under the action of the theta level group: transporting a Schrödinger frame by the intertwining matrix attached to an automorphism of the Heisenberg group again yields a Schrödinger frame, with lifts composed with $\gamma^{-1}$. It is the step used to construct the $\Gamma$-action on theta-adapted framings, and is cited in the proof that this finite group acts freely and transitively on them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_isThetaAdapted_of_isReframe_inter.lean

import Definitions.Def_AlgebraicGeometry_ThetaReframe
import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.isThetaAdapted_of_isReframe_inter
    (g N n : ℕ) (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = N + 1)
    (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (B : Type) [CommRing B] (hd : IsUnit ((N + 1 : ℕ) : B))
    (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : B) (hω : ω ^ 2 = ζ)
    {S : Type} [CommRing S] (φB : B →+* S) (γ : (ThetaLevel.Heis.Gam (δ := δ) (d := N + 1)))
    (X X' : FramedPolarisedAbelianScheme g N n S)
    (hre : X.IsReframe ((Matrix.transpose (ThetaLevel.inter δ (N + 1) B ω e ((γ)⁻¹).1)).map φB) X') (hX : X.IsThetaAdapted δ e) :
    X'.IsThetaAdapted δ e := by sorry

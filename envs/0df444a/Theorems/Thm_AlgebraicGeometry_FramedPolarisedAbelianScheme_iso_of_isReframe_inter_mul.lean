-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_of_isReframe_inter_mul
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_of_isReframe_inter_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/0222919a-e43b-57d4-a71f-7a25a5e8de8b
-- title:
--   Reframing by intertwiners is multiplicative up to framed isomorphism
-- statement:
--   Fix natural numbers $g, N, n$, a tuple $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with each $\delta_i$ nonzero and $\prod_i \delta_i = N+1$, and a bijection $e$ of $\mathrm{Fin}(N+1)$ with $\prod_i \mathbb{Z}/\delta_i$. Let $B$ be a commutative ring in which $N+1$ is a unit, let $\zeta \in B$ satisfy $\zeta^{N+1} = 1$ with $1 - \zeta^{j}$ a unit for all $0 < j < N+1$, and let $\omega \in B$ satisfy $\omega^{2} = \zeta$. Let $S$ be a commutative ring, $\varphi_B : B \to S$ a ring homomorphism, and $\gamma, \gamma'$ elements of the subgroup $\mathrm{Gam}$ of automorphisms of the Heisenberg group $\mathrm{Heis}\,\delta\,(N+1)$ fixing every central element. Let $X, X_1, X_2, X_3$ be framed polarised abelian schemes of type $(g,N,n)$ over $S$, that is, polarised abelian schemes of relative dimension $g$ with $n$-torsion frame of $2g$ points and invertible, very ample $\mathrm{pol}$ of geometric fibre $H^0$-rank $N+1$, equipped with a presentation into $\mathbb{P}^N_S$ whose structural morphism is a closed immersion and whose $N+1$ sections form a section basis. Assume that $X_1$ arises from $X$ by reframing along the transpose of $\mathrm{inter}\,\delta\,(N+1)\,B\,\omega\,e\,((\gamma\gamma')^{-1})$, with entries carried over by $\varphi_B$ — i.e. $X_1$ has the same underlying polarised abelian scheme as $X$ and its sections are the corresponding $S$-linear combinations of those of $X$ — that $X_2$ arises from $X$ by reframing along the transpose of $\mathrm{inter}$ at $(\gamma')^{-1}$, and that $X_3$ arises from $X_2$ by reframing along the transpose of $\mathrm{inter}$ at $\gamma^{-1}$. Then $X_1$ and $X_3$ are isomorphic as framed polarised abelian schemes: there is an isomorphism of their underlying schemes over $S$ compatible with the projective-space morphisms, with the relative group laws, with the $2g$ marked points, and locally on $\mathrm{Spec}\,S$ with the polarising modules.
--
--   This is the multiplicativity (cocycle) clause for the reframing operation attached to Heisenberg intertwiner matrices: reframing by $\mathrm{inter}((\gamma\gamma')^{-1})$ agrees, up to framed isomorphism, with reframing by $\mathrm{inter}((\gamma')^{-1})$ followed by reframing by $\mathrm{inter}(\gamma^{-1})$, the scalar ambiguity of intertwiners being invisible in the projective frame. It is used in the construction of the action of the theta group $\mathrm{Gam}$ on theta-adapted framed polarised abelian schemes, namely by [`AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_finite_group_action_isThetaAdapted_free_transitive_of_sq_eq`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_finite_group_action_isThetaAdapted_free_transitive_of_sq_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_of_isReframe_inter_mul.lean

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

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_of_isReframe_inter_mul
    (g N n : ℕ) (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = N + 1)
    (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (B : Type) [CommRing B] (hd : IsUnit ((N + 1 : ℕ) : B))
    (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : B) (hω : ω ^ 2 = ζ)
    {S : Type} [CommRing S] (φB : B →+* S) (γ γ' : (ThetaLevel.Heis.Gam (δ := δ) (d := N + 1)))
    (X X₁ X₂ X₃ : FramedPolarisedAbelianScheme g N n S)
    (h₁ : X.IsReframe ((Matrix.transpose (ThetaLevel.inter δ (N + 1) B ω e ((γ * γ')⁻¹).1)).map φB) X₁)
    (h₂ : X.IsReframe ((Matrix.transpose (ThetaLevel.inter δ (N + 1) B ω e ((γ')⁻¹).1)).map φB) X₂) (h₃ : X₂.IsReframe ((Matrix.transpose (ThetaLevel.inter δ (N + 1) B ω e ((γ)⁻¹).1)).map φB) X₃) :
    FramedPolarisedAbelianScheme.Iso X₁ X₃ := by sorry

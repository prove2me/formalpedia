-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_eq_one_of_isReframe_inter_of_iso
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.eq_one_of_isReframe_inter_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/9f8b368d-705f-5c2e-ba68-e61ee0a0a106
-- title:
--   Freeness of the theta group action on framed objects
-- statement:
--   Fix natural numbers $g,N,n$ and $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with all $\delta_i$ non-zero and $\prod_i \delta_i = N+1$, together with a bijection $e$ of $\mathrm{Fin}(N+1)$ with $H(\delta) = \prod_i \mathbb{Z}/\delta_i$. Let $B$ be a commutative ring in which $N+1$ is a unit, let $\zeta \in B$ satisfy $\zeta^{N+1}=1$ with $1-\zeta^{j}$ a unit for $0<j<N+1$, and let $\omega \in B$ satisfy $\omega^2 = \zeta$; assume $n \ge 3$ and $n$ a unit in $B$. Assume further (`hint`) that every element $\gamma$ of the group $\Gamma =$ `ThetaLevel.Heis.Gam` of automorphisms of the Heisenberg group $\mathrm{Heis}(\delta, N+1)$ fixing all central elements admits an intertwiner over $B$: an invertible $(N+1)\times(N+1)$ matrix $U$ with $U\,\vartheta(z) = \vartheta(\gamma z)\,U$ for all $z$, where $\vartheta =$ `ThetaLevel.schrodMat` is the Schrödinger matrix representation attached to $(\delta, N+1, B, \omega, e)$. Let $S$ be a non-trivial commutative ring, $\varphi_B : B \to S$ a ring homomorphism, $\gamma \in \Gamma$, and let $X, X'$ be framed polarised abelian schemes of type $(g,N,n)$ over $S$, that is, polarised abelian schemes of relative fibre dimension $g$ with geometric $H^0$ of the polarisation of rank $N+1$ and a marked basis of $n$-torsion sections, equipped with a projective presentation of the polarisation by $N+1$ sections which is a closed immersion and whose sections form a section basis on the whole space. Assume $X$ is theta-adapted for $(\delta, e)$ (its frame sections correspond, under $e$, to the sections of a Schrödinger frame for $X$), and assume `X.IsReframe` holds for the matrix $\varphi_B$ applied entrywise to the transpose of `ThetaLevel.inter` $\delta\,(N+1)\,B\,\omega\,e\,(\gamma^{-1})$ and for $X'$: that is, $X'$ has the same underlying polarised abelian scheme as $X$ and its frame sections are the corresponding $S$-linear combinations of those of $X$. If $X'$ and $X$ are isomorphic as framed polarised abelian schemes (an isomorphism of the underlying schemes over $S$ commuting with the group laws, matching the marked torsion sections, matching the two morphisms to projective space, and locally matching the polarisations), then $\gamma = 1$.
--
--   This is the freeness clause for the action of the theta-level group $\Gamma_\delta$ on framed theta-structures: reframing by a non-trivial $\gamma$ cannot return an isomorphic framed object over a non-zero base. It is used in the construction of the free and transitive finite group action on theta-adapted framed polarised abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_eq_one_of_isReframe_inter_of_iso.lean

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

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.eq_one_of_isReframe_inter_of_iso
    (g N n : ℕ) (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = N + 1)
    (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (B : Type) [CommRing B] (hd : IsUnit ((N + 1 : ℕ) : B))
    (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : B) (hω : ω ^ 2 = ζ)
    (hn : 3 ≤ n) (hn' : IsUnit ((n : ℕ) : B))
    (hint : ∀ γ : (ThetaLevel.Heis.Gam (δ := δ) (d := N + 1)), ∃ U : Matrix (Fin (N + 1)) (Fin (N + 1)) B, ThetaLevel.IsIntertwiner δ (N + 1) B ω e γ.1 U)
    {S : Type} [CommRing S] [Nontrivial S] (φB : B →+* S) (γ : (ThetaLevel.Heis.Gam (δ := δ) (d := N + 1)))
    (X X' : FramedPolarisedAbelianScheme g N n S) (hX : X.IsThetaAdapted δ e)
    (hre : X.IsReframe ((Matrix.transpose (ThetaLevel.inter δ (N + 1) B ω e ((γ)⁻¹).1)).map φB) X') (hiso : FramedPolarisedAbelianScheme.Iso X' X) :
    γ = 1 := by sorry

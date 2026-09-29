-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_cover_isReframe_inter_iso_of_isThetaAdapted_of_iso
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_cover_isReframe_inter_iso_of_isThetaAdapted_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/aacb7cfc-d426-50d0-92ea-70a5f104505f
-- title:
--   Theta-adapted frames differ locally by the theta group
-- statement:
--   Fix $g,N,n\in\mathbb N$, a tuple $\delta:\mathrm{Fin}\,g\to\mathbb N$ with each $\delta_i$ nonzero and $\prod_i\delta_i=N+1$, and a bijection $e:\mathrm{Fin}(N+1)\simeq\prod_i\mathbb Z/\delta_i$. Let $B$ be a commutative ring in which $N+1$ is invertible, carrying $\zeta$ with $\zeta^{N+1}=1$ and $1-\zeta^{j}$ a unit for $0<j<N+1$, and $\omega$ with $\omega^{2}=\zeta$; assume $3\le n$, that $n$ is a unit in $B$, and that every element $\gamma$ of the subgroup $\mathrm{Gam}$ of automorphisms of the Heisenberg group $\mathrm{Heis}\,\delta\,(N+1)$ fixing the central elements admits an intertwiner over $B$, i.e. a unit matrix $U$ of size $N+1$ with $U\cdot\mathrm{schrodMat}(z)=\mathrm{schrodMat}(\gamma z)\cdot U$ for all $z$. Let $\varphi_B:B\to S$ be a ring map, and let $X,X'$ be framed polarised abelian schemes of relative dimension $g$, degree $N+1$ and level $n$ over $S$ (a polarised abelian scheme with $2g$ $n$-torsion sections, together with a projective presentation of $\mathrm{pol}$ by $N+1$ sections that is a closed immersion and a section basis), both theta-adapted for $(\delta,e)$ — their frame sections are, via $e$, the sections of a Schrödinger frame — and suppose their underlying polarised abelian schemes are isomorphic (an isomorphism over $S$ compatible with the group laws, the torsion sections, and locally on the base with the polarisations). Then there are finitely many $r_1,\dots,r_m\in S$ generating the unit ideal such that for each $j$ and any framed polarised abelian schemes $Y,Y'$ over $S[1/r_j]$ obtained as base changes of $X$ and $X'$ along $S\to S[1/r_j]$, there exists $\gamma\in\mathrm{Gam}$ with the property that every $Y''$ obtained from $Y$ by reframing with the matrix $\mathrm{inter}\,\delta\,(N+1)\,B\,\omega\,e\,(\gamma^{-1})$ transposed and mapped entrywise along $S[1/r_j]\circ\varphi_B$ — that is, every $Y''$ whose frame sections are the corresponding linear combinations of those of $Y$ — is isomorphic to $Y'$ as a framed polarised abelian scheme.
--
--   This is the rigidity clause for theta structures: two theta-adapted framings of one polarised abelian scheme over $S$ agree, Zariski-locally on $S$, up to the action of the theta-level group $\mathrm{Gam}$ through its Schrödinger intertwiners. It feeds the construction of the free transitive action of that finite group on theta-adapted framings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_cover_isReframe_inter_iso_of_isThetaAdapted_of_iso.lean

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

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_cover_isReframe_inter_iso_of_isThetaAdapted_of_iso
    (g N n : ℕ) (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = N + 1)
    (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (B : Type) [CommRing B] (hd : IsUnit ((N + 1 : ℕ) : B))
    (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : B) (hω : ω ^ 2 = ζ)
    (hn : 3 ≤ n) (hn' : IsUnit ((n : ℕ) : B))
    (hint : ∀ γ : (ThetaLevel.Heis.Gam (δ := δ) (d := N + 1)), ∃ U : Matrix (Fin (N + 1)) (Fin (N + 1)) B, ThetaLevel.IsIntertwiner δ (N + 1) B ω e γ.1 U)
    {S : Type} [CommRing S] (φB : B →+* S)
    (X X' : FramedPolarisedAbelianScheme g N n S) (hX : X.IsThetaAdapted δ e) (hX' : X'.IsThetaAdapted δ e)
    (hiso : PolarisedAbelianScheme.Iso X.toPolarisedAbelianScheme X'.toPolarisedAbelianScheme) :
    ∃ (m : ℕ) (r : Fin m → S), Ideal.span (Set.range r) = ⊤ ∧ ∀ (j : Fin m)
      (Y Y' : FramedPolarisedAbelianScheme g N n (Localization.Away (r j))),
      FramedPolarisedAbelianScheme.IsPullback (algebraMap S (Localization.Away (r j))) X Y →
      FramedPolarisedAbelianScheme.IsPullback (algebraMap S (Localization.Away (r j))) X' Y' →
      ∃ γ : (ThetaLevel.Heis.Gam (δ := δ) (d := N + 1)), ∀ Y'' : FramedPolarisedAbelianScheme g N n (Localization.Away (r j)),
        Y.IsReframe ((Matrix.transpose (ThetaLevel.inter δ (N + 1) B ω e ((γ)⁻¹).1)).map ((algebraMap S (Localization.Away (r j))).comp φB)) Y'' →
        FramedPolarisedAbelianScheme.Iso Y'' Y' := by sorry

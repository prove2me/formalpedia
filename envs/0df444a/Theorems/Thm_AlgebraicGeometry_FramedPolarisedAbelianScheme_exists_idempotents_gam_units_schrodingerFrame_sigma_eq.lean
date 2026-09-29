-- Prove2me | Theorems.Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_idempotents_gam_units_schrodingerFrame_sigma_eq
-- name    : AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_idempotents_gam_units_schrodingerFrame_sigma_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/7a2c1d9e-6938-5cd4-800e-98558077ab66
-- title:
--   Two Schrödinger frames differ clopen-locally by an intertwiner matrix
-- statement:
--   Fix $g, N, n \in \mathbb{N}$ and $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with every $\delta_i$ nonzero and $\prod_i \delta_i = N+1$, together with a bijection $e : \mathrm{Fin}(N+1) \simeq H := \prod_i \mathbb{Z}/\delta_i$. Let $B$ be a commutative ring in which $N+1$ is invertible, $\zeta \in B$ with $\zeta^{N+1} = 1$ and $1 - \zeta^{j}$ invertible for $0 < j < N+1$, and $\omega \in B$ with $\omega^{2} = \zeta$; assume that every $\gamma$ in the group $\mathrm{Gam}$ of automorphisms of the Heisenberg group $\mathrm{Heis}\,\delta\,(N+1)$ fixing all central elements admits an intertwiner, i.e. an invertible matrix $U \in M_{N+1}(B)$ with $U \cdot \mathrm{schrodMat}(z) = \mathrm{schrodMat}(\gamma z) \cdot U$ for all $z$. Let $\varphi_B : B \to S$ be a ring homomorphism into a commutative ring $S$, let $X$ be a framed polarised abelian scheme of type $(g, N, n)$ over $S$ (a polarised abelian scheme $X.f : A \to \operatorname{Spec} S$ with group law $X.L$, invertible sheaf $X.\mathrm{pol}$ and a projective presentation by $N+1$ sections), and let $F, F'$ be two Schrödinger frames of type $\delta$ for $(X.f, X.L, X.\mathrm{pol})$ over the identity of $\operatorname{Spec} S$, each consisting of sections $\sigma_h$ indexed by $H$ that form a basis over the base, together with lifts of translations by $H$ and of additive characters of $H$ to theta-points acting on the $\sigma_h$ in the prescribed way. Then there exist $m \in \mathbb{N}$, elements $\varepsilon_1, \dots, \varepsilon_m \in S$ that are idempotent, sum to $1$ and are pairwise orthogonal, elements $\gamma_1, \dots, \gamma_m \in \mathrm{Gam}$, and a unit $c \in S^{\times}$, such that for every $i \in \mathrm{Fin}(N+1)$,
--   $$F'.\sigma(e\,i) = \sum_{j} \Big(\sum_{k} \varepsilon_k\, c\, \varphi_B\big(\mathrm{inter}\,\delta\,(N+1)\,B\,\omega\,e\,(\gamma_k^{-1})_{j i}\big)\Big) \cdot F.\sigma(e\,j),$$
--   where $\mathrm{inter}$ denotes the chosen intertwiner matrix and the scalars act through the structure map $\mathrm{baseScalar}$.
--
--   This is the comparison statement for theta-level frames: after decomposing $\operatorname{Spec} S$ into the finitely many clopen pieces cut out by a complete orthogonal family of idempotents, any two Schrödinger frames of the same type $\delta$ on a framed polarised abelian scheme differ by a single unit times the transposed intertwiner matrix of an element of the theta level group $\mathrm{Gam}$. It feeds the construction of coverings on which a frame becomes a reframe of another by such an intertwiner, used in the theta-adapted rigidification of polarised abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_idempotents_gam_units_schrodingerFrame_sigma_eq.lean

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

theorem AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_idempotents_gam_units_schrodingerFrame_sigma_eq
    (g N n : ℕ) (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = N + 1)
    (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (B : Type) [CommRing B] (hd : IsUnit ((N + 1 : ℕ) : B))
    (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : B) (hω : ω ^ 2 = ζ)
    (hint : ∀ γ : (ThetaLevel.Heis.Gam (δ := δ) (d := N + 1)), ∃ U : Matrix (Fin (N + 1)) (Fin (N + 1)) B, ThetaLevel.IsIntertwiner δ (N + 1) B ω e γ.1 U)
    {S : Type} [CommRing S] (φB : B →+* S) (X : FramedPolarisedAbelianScheme g N n S)
    (F F' : Polarisation.SchrodingerFrame X.f X.L X.pol (𝟙 (Spec (CommRingCat.of S))) δ) :
    ∃ (m : ℕ) (ε : Fin m → S) (γ : Fin m → (ThetaLevel.Heis.Gam (δ := δ) (d := N + 1))) (c : Sˣ),
      (∀ k, IsIdempotentElem (ε k)) ∧ (∑ k, ε k = 1) ∧ (∀ k l, k ≠ l → ε k * ε l = 0) ∧
      ∀ i : Fin (N + 1), F'.σ (e i) =
        ∑ j : Fin (N + 1),
          Polarisation.baseScalar X.f (𝟙 (Spec (CommRingCat.of S)))
            (∑ k, ε k * (c : S) * φB ((Matrix.transpose (ThetaLevel.inter δ (N + 1) B ω e ((γ k)⁻¹).1)) i j)) •
          F.σ (e j) := by sorry

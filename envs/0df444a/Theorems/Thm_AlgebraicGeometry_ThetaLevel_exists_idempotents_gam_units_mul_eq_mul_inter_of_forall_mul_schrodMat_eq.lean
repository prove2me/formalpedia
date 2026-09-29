-- Prove2me | Theorems.Thm_AlgebraicGeometry_ThetaLevel_exists_idempotents_gam_units_mul_eq_mul_inter_of_forall_mul_schrodMat_eq
-- name    : AlgebraicGeometry.ThetaLevel.exists_idempotents_gam_units_mul_eq_mul_inter_of_forall_mul_schrodMat_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/355aa77e-6d90-5d60-92db-c8b6d033b0c8
-- title:
--   Piecewise: conjugators are units times chosen intertwiners
-- statement:
--   Fix $g$ and $\delta : \mathrm{Fin}\,g \to \mathbb{N}$ with every $\delta_i$ nonzero, and $N$ with $\prod_i \delta_i = N+1$, together with a bijection $e : \mathrm{Fin}(N+1) \simeq \prod_i \mathbb{Z}/\delta_i$. Let $B$ be a commutative ring in which $N+1$ is invertible, $\zeta \in B$ with $\zeta^{N+1} = 1$ and $1-\zeta^{j}$ a unit for all $0 < j < N+1$, and $\omega \in B$ with $\omega^{2} = \zeta$. Write $\vartheta_R(z)$ for the Schrödinger matrix `schrodMat` of $z = (a,h,k) \in \mathrm{Heis}_\delta(N+1)$ over a ring $R$, whose $(i,j)$ entry is $\omega^{(a + \mathrm{pair}(k, e j)).\mathrm{val}}$ when $e i = e j + h$ and $0$ otherwise. Assume (`hint`) that every $\gamma$ in the subgroup $\Gamma$ of automorphisms of $\mathrm{Heis}_\delta(N+1)$ fixing all central elements admits an intertwiner over $B$, i.e. an invertible $U$ with $U\,\vartheta_B(z) = \vartheta_B(\gamma z)\,U$ for all $z$. Let $\varphi_B : B \to S$ be a ring homomorphism to a commutative ring $S$, and let $T$ be an invertible $(N+1)\times(N+1)$ matrix over $S$ such that for each $z$ there are complete orthogonal idempotents $(\varepsilon_c)_{c \in H \times H}$ of $S$, $H = \prod_i \mathbb{Z}/\delta_i$, and a unit $u \in S^\times$ with $T\,\vartheta_S(z) = \bigl(\sum_c \varepsilon_c\, u\, \vartheta_S(0,c_1,c_2)\bigr) T$, the matrices over $S$ being formed with $\varphi_B(\omega)$. Then there exist $m$, complete orthogonal idempotents $\varepsilon_1,\dots,\varepsilon_m$ of $S$, elements $\gamma_1,\dots,\gamma_m \in \Gamma$ and a single unit $c \in S^\times$ such that $\varepsilon_k\, T = \varepsilon_k\, c\, \varphi_B\bigl(\mathrm{inter}(\gamma_k^{-1})\bigr)$ for every $k$, where $\mathrm{inter}$ denotes the chosen intertwiner matrix of an automorphism and $\varphi_B$ is applied entrywise.
--
--   This is the algebraic core of the statement that two theta structures on the same data differ by an element of the group of automorphisms of the Heisenberg group fixing its centre: a matrix conjugating the Schrödinger representation into piecewise monomial form is, on each piece of a decomposition of $\operatorname{Spec} S$ into idempotents, a unit multiple of the chosen intertwiner of a group element. It is used by [`AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_idempotents_gam_units_schrodingerFrame_sigma_eq`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_idempotents_gam_units_schrodingerFrame_sigma_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ThetaLevel_exists_idempotents_gam_units_mul_eq_mul_inter_of_forall_mul_schrodMat_eq.lean

import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

theorem AlgebraicGeometry.ThetaLevel.exists_idempotents_gam_units_mul_eq_mul_inter_of_forall_mul_schrodMat_eq
    {g : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (N : ℕ) (hδd : ∏ i, δ i = N + 1)
    (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (B : Type) [CommRing B] (hd : IsUnit ((N + 1 : ℕ) : B))
    (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : B) (hω : ω ^ 2 = ζ)
    (hint : ∀ γ : (Heis.Gam (δ := δ) (d := N + 1)), ∃ U : Matrix (Fin (N + 1)) (Fin (N + 1)) B, IsIntertwiner δ (N + 1) B ω e γ.1 U)
    {S : Type} [CommRing S] (φB : B →+* S)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) S) (hT : IsUnit T)
    (hmono : ∀ z : Heis δ (N + 1), ∃ (ε : ((i : Fin g) → ZMod (δ i)) × ((i : Fin g) → ZMod (δ i)) → S) (u : Sˣ),
      CompleteOrthogonalIdempotents ε ∧
        T * schrodMat δ (N + 1) S (φB ω) e z =
          (∑ c, ε c • ((u : S) • schrodMat δ (N + 1) S (φB ω) e ⟨0, c.1, c.2⟩)) * T) :
    ∃ (m : ℕ) (ε : Fin m → S) (γ : Fin m → (Heis.Gam (δ := δ) (d := N + 1))) (c : Sˣ),
      CompleteOrthogonalIdempotents ε ∧
      ∀ k, ε k • T = ε k • ((c : S) • (ThetaLevel.inter δ (N + 1) B ω e ((γ k)⁻¹).1).map φB) := by sorry

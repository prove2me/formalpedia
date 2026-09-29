-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_chain_affine_edgeRegion_cover_affinoid
-- name    : CerednikDrinfeld.Omega.exists_chain_affine_edgeRegion_cover_affinoid
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/64d7cb21-7b4a-57f9-91b6-7fe51e69b671
-- title:
--   Affine edge-region chain cover of the Drinfeld affinoid
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$, let $C$ be a field extension of $K_0$ carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, and let $\varpi$ be a pseudo-uniformiser of $K_0$ in $C$, i.e. an element $\varpi.\varpi \in K_0$ with $0 < v(\varpi.\varpi) < 1$ in $C$ and such that every nonzero $a \in K_0$ satisfies $v(\varpi.\varpi)^N \le v(a) \le v(\varpi.\varpi)^{-N}$ for some $N$. Assume $\varpi_0 \in R$ is irreducible with $\varpi.\varpi$ its image in $K_0$, that $R/(\varpi_0)$ is finite, that every element of $R$ has valuation $\le 1$ in $C$, and conversely that every $a \in K_0$ with $v(a) \le 1$ lies in the image of $R$; let $n \ge 1$. Then there exist $k \in \mathbb{N}$, sets $P_j \subseteq C$, elements $g_j \in \mathrm{GL}_2(K_0)$, centres $t_j \in C$, radii $\pi_j \in C$ and finite sets $Z_j \subseteq C$, indexed by $j \in \mathrm{Fin}(k+1)$, such that: (i) $P_j$ is the closed edge region $\mathrm{vertexTube}(\bar g_j) \cup \mathrm{edgeTube}(\bar g_j) \cup \mathrm{vertexTube}(\bar g_j \sigma)$, where $\bar g$ denotes the class of $g$ in $\mathrm{PGL}_2(K_0)$, $\sigma = \mathrm{edgeFlip}$ is the diagonal matrix $\mathrm{diag}(\varpi.\varpi, 1)$, $\mathrm{vertexTube}(h)$ is the set of $z \in C$ outside the image of $K_0$ whose Möbius image under $h^{-1}$ lies in $\mathrm{affinoid}\,\varpi\,0$, and $\mathrm{edgeTube}(h)$ is the set of such $z$ whose Möbius image under $h^{-1}$ lies outside the image of $K_0$ and has valuation strictly between $v(\varpi.\varpi)$ and $1$; (ii) each $g_j$ is represented by an affine matrix $\begin{pmatrix} \varpi.\varpi^{\,m-1} & c \\ 0 & 1\end{pmatrix}$ with $c \in K_0$, $m \in \mathbb{Z}$; (iii) each $P_j$ is contained in $\mathrm{affinoid}\,\varpi\,n = \{z : v(z) \le v(\varpi.\varpi)^{-n}$ and $v(\varpi.\varpi)^n \le v(z-a)$ for all $a \in K_0$ with $v(a) \le v(\varpi.\varpi)^{-n}\}$, and this affinoid is the union of the $P_j$; and (iv) for every $j \ne 0$: $\pi_j \ne 0$; every point of every earlier $P_i$ ($i < j$) satisfies $v(\pi_j) \le v(z - t_j)$; every $z \in P_j$ either lies in an earlier $P_i$ or satisfies $v(z - t_j) < v(\pi_j)$; and every $z \in C$ with $v(z - t_j) = v(\pi_j)$ and $v(\pi_j) \le v(z - \zeta)$ for all $\zeta \in Z_j$ lies in $P_j$ and also in some earlier $P_i$. No conditions are imposed on $t_0$, $\pi_0$, $Z_0$.
--
--   This is the finite covering of the affinoid $\Omega_n$ of Drinfeld's upper half plane by closed edge regions of the Bruhat–Tits tree, taken for affine charts only and enumerated as a chain in which each region meets the union of its predecessors along a prescribed annulus, which is the shape required by the chain-gluing criterion for holomorphic functions. It is used in the construction of holomorphic functions on $\Omega_n$ compatible with the Čerednik–Drinfeld uniformisation, in [`CerednikDrinfeld.exists_holOn_affinoid_mul_pullback_eq_of_cover_clearing_of_cerednikDrinfeld_quotient`](thm.html#CerednikDrinfeld.exists_holOn_affinoid_mul_pullback_eq_of_cover_clearing_of_cerednikDrinfeld_quotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_chain_affine_edgeRegion_cover_affinoid.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_chain_affine_edgeRegion_cover_affinoid
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (C : Type) [Field C] [Algebra K₀ C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    (ϖ : PseudoUniformizer K₀ C) (ϖ₀ : R) (hϖ₀ : Irreducible ϖ₀) (hϖ : ϖ.ϖ = algebraMap R K₀ ϖ₀)
    [Finite (R ⧸ Ideal.span {ϖ₀})]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ C (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ C a) ≤ 1 → IsLocalization.IsInteger R a)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ (k : ℕ) (P : Fin (k + 1) → Set C) (g : Fin (k + 1) → GL (Fin 2) K₀)
      (t π : Fin (k + 1) → C) (Z : Fin (k + 1) → Finset C),

      (∀ j, P j = (vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g j)) ∪ edgeTube ϖ (Matrix.ProjGenLinGroup.mk (g j)) ∪
            vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g j * edgeFlip K₀ ϖ)))) ∧

      (∀ j, ∃ (c : K₀) (m : ℤ), ((g j : GL (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = !![ϖ.ϖ ^ (m - 1), c; 0, 1]) ∧

      (∀ j, P j ⊆ affinoid ϖ n) ∧ (affinoid ϖ n ⊆ ⋃ j, P j) ∧

      (∀ j, j ≠ 0 → π j ≠ 0) ∧
      (∀ j, j ≠ 0 → ∀ i, i < j → ∀ z ∈ P i, Valued.v (π j) ≤ Valued.v (z - t j)) ∧
      (∀ j, j ≠ 0 → ∀ z ∈ P j, (∃ i, i < j ∧ z ∈ P i) ∨ Valued.v (z - t j) < Valued.v (π j)) ∧
      (∀ j, j ≠ 0 → ∀ z : C, Valued.v (z - t j) = Valued.v (π j) →
        (∀ ζ ∈ Z j, Valued.v (π j) ≤ Valued.v (z - ζ)) → z ∈ P j ∧ ∃ i, i < j ∧ z ∈ P i) := by sorry

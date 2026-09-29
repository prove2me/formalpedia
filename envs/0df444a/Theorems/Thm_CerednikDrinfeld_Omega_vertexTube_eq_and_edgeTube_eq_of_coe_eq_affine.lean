-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_vertexTube_eq_and_edgeTube_eq_of_coe_eq_affine
-- name    : CerednikDrinfeld.Omega.vertexTube_eq_and_edgeTube_eq_of_coe_eq_affine
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/e2da9bcc-a9cb-56b6-93bd-7457431a0c57
-- title:
--   Vertex and edge tubes of an affine chart, explicitly
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$, let $C$ be a field extension of $K_0$ with decidable equality carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, and let $\varpi$ be a pseudo-uniformiser for $K_0$ in $C$, i.e. an element $\varpi.\varpi \in K_0$ whose image in $C$ has $0 < v < 1$ and such that every nonzero $a \in K_0$ satisfies $v(\varpi.\varpi)^N \le v(a) \le v(\varpi.\varpi)^{-N}$ for some $N \in \mathbb{N}$. Assume $\varpi.\varpi$ is the image of an irreducible $\varpi_0 \in R$, that $R/(\varpi_0)$ is finite, that every element of $R$ has valuation $\le 1$ in $C$, and conversely that every $a \in K_0$ with $v(a) \le 1$ lies in the image of $R$. Fix $c \in K_0$, $m \in \mathbb{Z}$ and $g \in \mathrm{GL}_2(K_0)$ whose matrix is $\begin{pmatrix}\varpi^{m-1} & c \\ 0 & 1\end{pmatrix}$ with $\varpi = \varpi.\varpi$. Writing $\bar g$ for the class of $g$ in $\mathrm{PGL}(2,K_0)$, the three sets are computed. First, $\mathrm{vertexTube}\,\varpi\,\bar g$, the set of $z \in C$ outside the image of $K_0$ whose image under the Möbius action of $\bar g^{-1}$ lies in $\mathrm{affinoid}\,\varpi\,0$, equals $\{z : v(z-c) \le v(\varpi^{m-1}) \text{ and } v(\varpi^{m-1}) \le v(z-a) \text{ for all } a \in K_0\}$. Second, $\mathrm{edgeTube}\,\varpi\,\bar g$, defined by the same condition with $\mathrm{affinoid}\,\varpi\,0$ replaced by $\mathrm{stdEdgeTube}\,\varpi$, equals the annulus $\{z : v(\varpi^{m}) < v(z-c) < v(\varpi^{m-1})\}$. Third, $\mathrm{vertexTube}\,\varpi$ of the class of $g\cdot\mathrm{edgeFlip}$, with $\mathrm{edgeFlip} = \mathrm{diag}(\varpi,1)$, equals $\{z : v(z-c) \le v(\varpi^{m}) \text{ and } v(\varpi^{m}) \le v(z-a) \text{ for all } a \in K_0\}$. Here all valuations are taken after applying $K_0 \to C$, and the universally quantified clauses in the first and third descriptions force $z$ to lie outside $K_0$.
--
--   This identifies the tubes attached to the affine chart $w \mapsto \varpi^{m-1}w + c$ of Drinfeld's upper half-plane with explicit closed discs from which the open residue discs around all $K_0$-points have been removed, together with the intervening open annulus. It supplies the explicit shape of the pieces in the edge-region covers constructed in [`CerednikDrinfeld.Omega.exists_chain_affine_edgeRegion_cover_affinoid`](thm.html#CerednikDrinfeld.Omega.exists_chain_affine_edgeRegion_cover_affinoid) and [`CerednikDrinfeld.Omega.exists_finset_edgeRegion_eq_tube_and_pmoebius_inv_eq_of_coe_eq_affine`](thm.html#CerednikDrinfeld.Omega.exists_finset_edgeRegion_eq_tube_and_pmoebius_inv_eq_of_coe_eq_affine).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_vertexTube_eq_and_edgeTube_eq_of_coe_eq_affine.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.vertexTube_eq_and_edgeTube_eq_of_coe_eq_affine
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (C : Type) [Field C] [Algebra K₀ C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    (ϖ : PseudoUniformizer K₀ C) (ϖ₀ : R) (hϖ₀ : Irreducible ϖ₀) (hϖ : ϖ.ϖ = algebraMap R K₀ ϖ₀)
    [Finite (R ⧸ Ideal.span {ϖ₀})]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ C (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ C a) ≤ 1 → IsLocalization.IsInteger R a)
    (c : K₀) (m : ℤ) (g : GL (Fin 2) K₀) (hg : (g : Matrix (Fin 2) (Fin 2) K₀) = !![ϖ.ϖ ^ (m - 1), c; 0, 1]) :
    vertexTube ϖ (Matrix.ProjGenLinGroup.mk g) =
        {z : C | Valued.v (z - algebraMap K₀ C c) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) ∧
          ∀ a : K₀, Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1))) ≤ Valued.v (z - algebraMap K₀ C a)} ∧
      edgeTube ϖ (Matrix.ProjGenLinGroup.mk g) =
        {z : C | Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m))) < Valued.v (z - algebraMap K₀ C c) ∧
          Valued.v (z - algebraMap K₀ C c) < Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m - 1)))} ∧
      vertexTube ϖ (Matrix.ProjGenLinGroup.mk (g * edgeFlip K₀ ϖ)) =
        {z : C | Valued.v (z - algebraMap K₀ C c) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m))) ∧
          ∀ a : K₀, Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (m))) ≤ Valued.v (z - algebraMap K₀ C a)} := by sorry

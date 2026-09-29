-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_chain_clauses_of_ballEdges
-- name    : CerednikDrinfeld.Omega.chain_clauses_of_ballEdges
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/0e626002-cd74-5a31-9b15-eff397854055
-- title:
--   Chain clauses for a breadth-first list of edge discs
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$, and let $C$ be a valued field extension of $K_0$ whose valuation $v$ takes values in a linearly ordered commutative group with zero. Let $\varpi$ be a pseudo-uniformizer of $K_0$ relative to $C$, i.e. an element $\varpi.\varpi \in K_0$ with $0 < v(\varpi.\varpi) < 1$ such that every nonzero $a \in K_0$ satisfies $v(\varpi.\varpi)^N \le v(a) \le v(\varpi.\varpi)^{-N}$ for some $N$; assume $\varpi.\varpi$ is the image of an irreducible $\varpi_0 \in R$, that $R/(\varpi_0)$ is finite, that every element of $R$ has valuation $\le 1$ in $C$, and that every $a \in K_0$ with $v(a) \le 1$ lies in the image of $R$. Fix $n, k \in \mathbb{N}$, centres $\mathrm{cen} : \mathrm{Fin}(k+1) \to K_0$ and levels $\mathrm{lev} : \mathrm{Fin}(k+1) \to \mathbb{Z}$ subject to: $\mathrm{lev}\,0 = 1-n$; every centre satisfies $v(\mathrm{cen}\,j) \le v(\varpi^{-n})$; $\mathrm{lev}\,j \ge 1-n$; $\mathrm{lev}$ is monotone for the order on $\mathrm{Fin}(k+1)$; distinct indices of equal level satisfy $v(\varpi^{\mathrm{lev}\,j}) < v(\mathrm{cen}\,i - \mathrm{cen}\,j)$; and each $j$ either has level $1-n$ or admits $i < j$ with $\mathrm{lev}\,i = \mathrm{lev}\,j - 1$ and $v(\mathrm{cen}\,j - \mathrm{cen}\,i) \le v(\varpi^{\mathrm{lev}\,j-1})$. Let $P_j \subseteq C$ be the union of: the points $z$ with $v(z - \mathrm{cen}\,j) \le v(\varpi^{\mathrm{lev}\,j-1})$ and $v(z-a) \ge v(\varpi^{\mathrm{lev}\,j-1})$ for all $a \in K_0$; the open annulus $v(\varpi^{\mathrm{lev}\,j}) < v(z-\mathrm{cen}\,j) < v(\varpi^{\mathrm{lev}\,j-1})$; and the points $z$ with $v(z-\mathrm{cen}\,j) \le v(\varpi^{\mathrm{lev}\,j})$ and $v(z-a) \ge v(\varpi^{\mathrm{lev}\,j})$ for all $a \in K_0$. Then, for every $j \neq 0$: the image of $\varpi^{\mathrm{lev}\,j-1}$ in $C$ is nonzero; every $z \in P_i$ with $i<j$ satisfies $v(z - \mathrm{cen}\,j) \ge v(\varpi^{\mathrm{lev}\,j-1})$; every $z \in P_j$ either lies in some $P_i$ with $i<j$ or satisfies $v(z - \mathrm{cen}\,j) < v(\varpi^{\mathrm{lev}\,j-1})$. Moreover there are finite sets $Z_j \subseteq C$ such that for $j \neq 0$, any $z$ with $v(z-\mathrm{cen}\,j) = v(\varpi^{\mathrm{lev}\,j-1})$ and $v(z-\zeta) \ge v(\varpi^{\mathrm{lev}\,j-1})$ for all $\zeta \in Z_j$ lies in $P_j$ and in $P_i$ for some $i<j$.
--
--   This is the ultrametric bookkeeping for a breadth-first enumeration of the discs attached to the edges of the Bruhat–Tits tree: the listed clauses say that the pieces $P_j$ avoid the holes cut out by earlier pieces, that each piece is contained in the earlier ones together with its own open parent disc, and that the generic points of the outer rim of $P_j$ are shared with an earlier piece. It is used by [`CerednikDrinfeld.Omega.exists_chain_affine_edgeRegion_cover_affinoid`](thm.html#CerednikDrinfeld.Omega.exists_chain_affine_edgeRegion_cover_affinoid) to produce a chain cover of an affinoid by edge regions in the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_chain_clauses_of_ballEdges.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.chain_clauses_of_ballEdges
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (C : Type) [Field C] [Algebra K₀ C] [DecidableEq C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    (ϖ : PseudoUniformizer K₀ C) (ϖ₀ : R) (hϖ₀ : Irreducible ϖ₀) (hϖ : ϖ.ϖ = algebraMap R K₀ ϖ₀)
    [Finite (R ⧸ Ideal.span {ϖ₀})]
    (hint : ∀ a : R, Valued.v (algebraMap K₀ C (algebraMap R K₀ a)) ≤ 1)
    (hv : ∀ a : K₀, Valued.v (algebraMap K₀ C a) ≤ 1 → IsLocalization.IsInteger R a)
    (n : ℕ) (k : ℕ) (cen : Fin (k + 1) → K₀) (lev : Fin (k + 1) → ℤ)
    (hlev0 : lev 0 = 1 - (n : ℤ))
    (hroot : ∀ j, Valued.v (algebraMap K₀ C (cen j)) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (-(n : ℤ)))))
    (hlow : ∀ j, 1 - (n : ℤ) ≤ lev j)
    (hmono : ∀ i j, i ≤ j → lev i ≤ lev j)
    (hdist : ∀ i j, i ≠ j → lev i = lev j →
      Valued.v (algebraMap K₀ C (ϖ.ϖ ^ lev j)) < Valued.v (algebraMap K₀ C (cen i) - algebraMap K₀ C (cen j)))
    (hpar : ∀ j, lev j = 1 - (n : ℤ) ∨ ∃ i, i < j ∧ lev i = lev j - 1 ∧
      Valued.v (algebraMap K₀ C (cen j) - algebraMap K₀ C (cen i)) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))))
    (P : Fin (k + 1) → Set C)
    (hP : ∀ j, P j = ({z : C | Valued.v (z - algebraMap K₀ C (cen j)) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) ∧
          ∀ a : K₀, Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) ≤ Valued.v (z - algebraMap K₀ C a)} ∪
        {z : C | Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j))) < Valued.v (z - algebraMap K₀ C (cen j)) ∧
          Valued.v (z - algebraMap K₀ C (cen j)) < Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1)))} ∪
        {z : C | Valued.v (z - algebraMap K₀ C (cen j)) ≤ Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j))) ∧
          ∀ a : K₀, Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j))) ≤ Valued.v (z - algebraMap K₀ C a)})) :
    (∀ j, j ≠ 0 → algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1)) ≠ 0) ∧
    (∀ j, j ≠ 0 → ∀ i, i < j → ∀ z ∈ P i,
      Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) ≤ Valued.v (z - algebraMap K₀ C (cen j))) ∧
    (∀ j, j ≠ 0 → ∀ z ∈ P j, (∃ i, i < j ∧ z ∈ P i) ∨
      Valued.v (z - algebraMap K₀ C (cen j)) < Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1)))) ∧
    ∃ Z : Fin (k + 1) → Finset C,
      ∀ j, j ≠ 0 → ∀ z : C, Valued.v (z - algebraMap K₀ C (cen j)) = Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) →
        (∀ ζ ∈ Z j, Valued.v (algebraMap K₀ C (ϖ.ϖ ^ (lev j - 1))) ≤ Valued.v (z - ζ)) → z ∈ P j ∧ ∃ i, i < j ∧ z ∈ P i := by sorry

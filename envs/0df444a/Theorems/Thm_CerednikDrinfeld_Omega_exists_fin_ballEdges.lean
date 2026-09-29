-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_fin_ballEdges
-- name    : CerednikDrinfeld.Omega.exists_fin_ballEdges
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/35f981a6-d03c-5f8d-abc5-0c996c09da0b
-- title:
--   Breadth-first enumeration of discs of levels 1-n through n
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K_0$ (the $R$-algebra structure on $K_0$ making it the field of fractions), let $\varpi_0 \in R$ be irreducible, assume the residue ring $R/(\varpi_0)$ is finite, and let $n \ge 1$ be a natural number. Then there exist $k \in \mathbb{N}$ and families $\mathrm{cen} : \mathrm{Fin}(k+1) \to K_0$ and $\mathrm{lev} : \mathrm{Fin}(k+1) \to \mathbb{Z}$ with the following seven properties, where an element of $K_0$ is called integral when it lies in the image of $R \to K_0$, i.e. satisfies `IsLocalization.IsInteger R`. First, $\mathrm{cen}\,0 = 0$ and $\mathrm{lev}\,0 = 1-n$. Second, $\mathrm{lev}$ is monotone for the order on $\mathrm{Fin}(k+1)$: $i \le j$ implies $\mathrm{lev}\,i \le \mathrm{lev}\,j$. Third, for distinct indices $i \ne j$ with $\mathrm{lev}\,i = \mathrm{lev}\,j$, the quotient $(\mathrm{cen}\,i - \mathrm{cen}\,j)/\varpi_0^{\mathrm{lev}\,j}$ is not integral. Fourth, for every $j$, either $\mathrm{lev}\,j = 1-n$, or there is $i < j$ with $\mathrm{lev}\,i = \mathrm{lev}\,j - 1$ and $(\mathrm{cen}\,j - \mathrm{cen}\,i)/\varpi_0^{\mathrm{lev}\,j-1}$ integral. Fifth, for every $j$ one has $1-n \le \mathrm{lev}\,j \le n$ and $\mathrm{cen}\,j \cdot \varpi_0^{n}$ integral. Finally, for every $c \in K_0$ and $m \in \mathbb{Z}$ with $1-n \le m \le n$ and $c\,\varpi_0^{n}$ integral, there is an index $j$ with $\mathrm{lev}\,j = m$ and $(c - \mathrm{cen}\,j)/\varpi_0^{m}$ integral. Here the powers $\varpi_0^{\mathrm{lev}\,j}$, $\varpi_0^{m}$ are integer powers of the image of $\varpi_0$ in the field $K_0$.
--
--   In the disc model of the Bruhat–Tits tree of $\mathrm{PGL}_2(K_0)$, the data $(\mathrm{cen}\,j, \mathrm{lev}\,j)$ record the closed discs $D(\mathrm{cen}\,j, |\varpi_0|^{-\mathrm{lev}\,j})$ of levels $1-n, \dots, n$ contained in $D(0,|\varpi_0|^{n-1})$, each exactly once (third and last clauses), enumerated breadth-first (second clause) with the parent of each disc occurring earlier (fourth clause); the enumeration is a finite combinatorial statement about the rings $R/\varpi_0^k R$. It is used to produce the chain of edge regions covering the affinoid pieces of the formal upper half plane, in [`CerednikDrinfeld.Omega.exists_chain_affine_edgeRegion_cover_affinoid`](thm.html#CerednikDrinfeld.Omega.exists_chain_affine_edgeRegion_cover_affinoid).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_fin_ballEdges.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_fin_ballEdges
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (ϖ₀ : R) (hϖ₀ : Irreducible ϖ₀) [Finite (R ⧸ Ideal.span {ϖ₀})]
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ (k : ℕ) (cen : Fin (k + 1) → K₀) (lev : Fin (k + 1) → ℤ),
      cen 0 = 0 ∧ lev 0 = 1 - (n : ℤ) ∧
      (∀ i j, i ≤ j → lev i ≤ lev j) ∧
      (∀ i j, i ≠ j → lev i = lev j → ¬ IsLocalization.IsInteger R ((cen i - cen j) / algebraMap R K₀ ϖ₀ ^ lev j)) ∧
      (∀ j, lev j = 1 - (n : ℤ) ∨
        ∃ i, i < j ∧ lev i = lev j - 1 ∧ IsLocalization.IsInteger R ((cen j - cen i) / algebraMap R K₀ ϖ₀ ^ (lev j - 1))) ∧
      (∀ j, (1 - (n : ℤ) ≤ lev j ∧ lev j ≤ (n : ℤ) ∧ IsLocalization.IsInteger R (cen j * algebraMap R K₀ ϖ₀ ^ n))) ∧
      (∀ (c : K₀) (m : ℤ), (1 - (n : ℤ) ≤ m ∧ m ≤ (n : ℤ) ∧ IsLocalization.IsInteger R (c * algebraMap R K₀ ϖ₀ ^ n)) →
        ∃ j, lev j = m ∧ IsLocalization.IsInteger R ((c - cen j) / algebraMap R K₀ ϖ₀ ^ m)) := by sorry

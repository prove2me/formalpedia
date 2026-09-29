-- Prove2me | Theorems.Thm_AlgebraicCurve_RROpens_exists_injective_forall_forall_mem_ell_sub_sum_single_add_eq_ell_of_lt_card
-- name    : AlgebraicCurve.RROpens.exists_injective_forall_forall_mem_ell_sub_sum_single_add_eq_ell_of_lt_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/ebdee9d5-f73b-5967-b44f-903bb2cb4ea4
-- title:
--   Block general position with exact drop of ℓ by e
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra satisfying `IsCurveOver K F`, i.e. every nonzero $f \in F$ has a principal divisor of degree zero, every place of $F/K$ has residue field finite over $K$, and $\Omega_{F/K}$ is free of rank one over $F$; here a place is a valuation subring of $F$ containing the image of $K$, different from $F$ itself and a principal ideal ring, its degree $v.\mathrm{deg}$ is $\dim_K$ of its residue field, a divisor is a finitely supported $\mathbb{Z}$-valued function on places, $\mathrm{degree}$ is the sum of its coefficients weighted by the degrees of the places, and $\mathrm{ell}(D) = \dim_K L(D)$ for the Riemann–Roch space $L(D)$. Given $N \in \mathbb{N}$ and divisors $D_0,\dots,D_{N-1}$, and natural numbers $e, \rho$ with $e \le \mathrm{ell}(D_k)$ and $\mathrm{degree}(D_k) \le \rho$ for all $k$; given a finite index type $\iota$ and a family $B_i$ of finite sets of places, each consisting of places of degree $1$, pairwise disjoint, with $\#B_i \le b$ for some $b \ge 1$; and assuming $N\rho b^{e} + e < \#\iota$: then there is an injective map $a \colon \{0,\dots,e-1\} \to \iota$ such that for every $k$ and every choice of places $v_j \in B_{a(j)}$ one has $\mathrm{ell}\bigl(D_k - \sum_{j} v_j\bigr) + e = \mathrm{ell}(D_k)$.
--
--   This is a general-position statement for blocks of rational places: under a counting hypothesis on the number of blocks one can select $e$ blocks all of whose transversals cut the dimension of the Riemann–Roch space of each of the given divisors by exactly $e$, with no genus or Riemann–Roch bound imposed. It is used in the construction of charts for relative Picard schemes, where it feeds the statement on the rank of $H^0$ and the vanishing of $H^1$ for line bundles in general position with respect to such blocks; the only curve-theoretic input it cites is the inequality $\mathrm{ell}(D) \le \mathrm{ell}(D - P) + \deg P$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RROpens_exists_injective_forall_forall_mem_ell_sub_sum_single_add_eq_ell_of_lt_card.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open AlgebraicCurve

theorem AlgebraicCurve.RROpens.exists_injective_forall_forall_mem_ell_sub_sum_single_add_eq_ell_of_lt_card
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    {N : ℕ} (D : Fin N → Divisor K F) (e ρ : ℕ)
    (hℓ : ∀ k, e ≤ ell (D k)) (hdeg : ∀ k, Divisor.degree (D k) ≤ ρ)
    {ι : Type w} [Fintype ι] [DecidableEq ι] (B : ι → Finset (Place K F))
    (hB : ∀ i, ∀ v ∈ B i, v.deg = 1) (hdisj : ∀ i i', i ≠ i' → Disjoint (B i) (B i'))
    {b : ℕ} (hb1 : 1 ≤ b) (hb : ∀ i, (B i).card ≤ b)
    (hcard : N * ρ * b ^ e + e < Fintype.card ι) :
    ∃ a : Fin e → ι, Function.Injective a ∧
      ∀ k, ∀ v : Fin e → Place K F, (∀ j, v j ∈ B (a j)) →
        ell (D k - ∑ j : Fin e, Finsupp.single (v j) 1) + e = ell (D k) := by sorry

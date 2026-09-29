-- Prove2me | Theorems.Thm_AlgebraicCurve_RROpens_exists_injective_forall_forall_mem_ell_sub_sum_single_eq_one_of_lt_card
-- name    : AlgebraicCurve.RROpens.exists_injective_forall_forall_mem_ell_sub_sum_single_eq_one_of_lt_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/6cb6f844-b89b-5355-9d4c-b329759c4975
-- title:
--   Block form of simultaneous general position for ℓ(D-sum vⱼ)=1
-- statement:
--   Let $F$ be a field extension of a field $K$ which is a curve over $K$ in the project's sense, i.e. every nonzero $f \in F$ has a degree-zero divisor of valuations, each place of $F/K$ has residue field finite over $K$, and $\Omega[F/K]$ is free of rank one over $F$; here a place is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself and a principal ideal ring, a divisor is a finitely supported function from places to $\mathbb{Z}$, the degree of a divisor is $\sum_v D(v)\,\deg v$ with $\deg v = [\,v\text{'s residue field} : K\,]$, and $\ell(D)$ denotes the $K$-dimension of the Riemann–Roch space of $D$. Assume given a divisor $K_c$ and $g \in \mathbb{N}$ with $\ell(D) - \ell(K_c - D) = \deg D + 1 - g$ for all divisors $D$, and $r \in \mathbb{N}$ with $2g \le r+1$. Let $D_0,\dots,D_{N-1}$ be divisors, each of degree exactly $r$. Let $\iota$ be a finite index type and $B : \iota \to$ finite sets of places such that every place in every $B_i$ has degree $1$ and the $B_i$ are pairwise disjoint, and let $b \ge 1$ bound all cardinalities $\#B_i$. Assume $N r b^{\,r-g} + (r-g) < \#\iota$, with $r-g$ truncated subtraction of naturals. Then there is an injective $a : \{0,\dots,r-g-1\} \to \iota$ such that for every $k$ and every choice of places $v_j \in B_{a(j)}$ one has $\ell\bigl(D_k - \sum_j \mathbf{1}_{v_j}\bigr) = 1$, where $\mathbf{1}_{v}$ is the divisor taking the value $1$ at $v$ and $0$ elsewhere (the $v_j$ are automatically pairwise distinct, by injectivity of $a$ and disjointness of the blocks).
--
--   This is a general-position statement for Riemann–Roch spaces in block form: instead of choosing single places in general position with respect to finitely many divisors of degree $r$, one chooses whole pairwise disjoint blocks of degree-one places so that every transversal of the chosen blocks is simultaneously good for all the $D_k$. It is used in the construction of charts for relative Picard schemes, being cited by [`AlgebraicGeometry.RelPicard.exists_injective_forall_subsingleton_H1_sectionsOf_tensor_of_isAlgEquivZero_of_lt_card`](thm.html#AlgebraicGeometry.RelPicard.exists_injective_forall_subsingleton_H1_sectionsOf_tensor_of_isAlgEquivZero_of_lt_card).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RROpens_exists_injective_forall_forall_mem_ell_sub_sum_single_eq_one_of_lt_card.lean

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

theorem AlgebraicCurve.RROpens.exists_injective_forall_forall_mem_ell_sub_sum_single_eq_one_of_lt_card
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    {Kc : Divisor K F} {g : ℕ}
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    {r : ℕ} (hgr : 2 * g ≤ r + 1)
    {N : ℕ} (D : Fin N → Divisor K F) (hdeg : ∀ k, Divisor.degree (D k) = r)
    {ι : Type w} [Fintype ι] [DecidableEq ι] (B : ι → Finset (Place K F))
    (hB : ∀ i, ∀ v ∈ B i, v.deg = 1) (hdisj : ∀ i i', i ≠ i' → Disjoint (B i) (B i'))
    {b : ℕ} (hb1 : 1 ≤ b) (hb : ∀ i, (B i).card ≤ b)
    (hcard : N * r * b ^ (r - g) + (r - g) < Fintype.card ι) :
    ∃ a : Fin (r - g) → ι, Function.Injective a ∧
      ∀ k, ∀ v : Fin (r - g) → Place K F, (∀ j, v j ∈ B (a j)) →
        ell (D k - ∑ j : Fin (r - g), Finsupp.single (v j) 1) = 1 := by sorry

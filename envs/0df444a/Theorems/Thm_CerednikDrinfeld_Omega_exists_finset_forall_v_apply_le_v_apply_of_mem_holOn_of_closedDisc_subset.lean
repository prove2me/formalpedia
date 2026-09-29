-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_finset_forall_v_apply_le_v_apply_of_mem_holOn_of_closedDisc_subset
-- name    : CerednikDrinfeld.Omega.exists_finset_forall_v_apply_le_v_apply_of_mem_holOn_of_closedDisc_subset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/14294bbd-8c0d-5380-a39c-ab5ebb8152e2
-- title:
--   Maximum principle: a generic rim point dominates the closed disc
-- statement:
--   Let $K$ be a field carrying a valuation $v =$ `Valued.v` with values in a linearly ordered commutative group with zero $\Gamma_0$, and assume $K$ is algebraically closed. Let $S \subseteq K$ be a subset, and let $c, r \in K$ with $r \neq 0$ be such that $S$ contains the closed disc of radius $v(r)$ about $c$, i.e. every $z \in K$ with $v(z - c) \le v(r)$ lies in $S$. Let $g : S \to K$ be a member of the subring `holOn K S`, that is, there is a sequence $(R_k)_{k \in \mathbb{N}}$ of rational pairs over $K$, each without poles on $S$, whose values on $S$ are uniformly bounded in valuation by $v(b)$ for a single $b \in K$, and whose evaluations converge uniformly on $S$ to $g$. The conclusion is that there is a finite set $E \subseteq K$ with the following property: for every $z_0 \in K$ with $v(z_0 - c) = v(r)$ satisfying $v(r) \le v(z_0 - e)$ for all $e \in E$, one has $v(g(z)) \le v(g(z_0))$ for every $z \in K$ with $v(z - c) \le v(r)$. No completeness or discreteness assumption is made on $K$ or on $\Gamma_0$.
--
--   This is the non-archimedean maximum principle for a function holomorphic in the sense of bounded uniform approximation by pole-free rational functions: the supremum of $v(g)$ over the closed disc is attained, and attained at every rim point lying outside finitely many residue discs of radius $v(r)$. It is used in the study of Drinfeld's rigid-analytic upper half plane, where it feeds the factorisation of a holomorphic function as a product of linear factors times a nowhere-vanishing function, both on an affinoid and under the hypothesis of finitely many zeros.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_finset_forall_v_apply_le_v_apply_of_mem_holOn_of_closedDisc_subset.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_finset_forall_v_apply_le_v_apply_of_mem_holOn_of_closedDisc_subset
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (S : Set K) (c r : K) (hr : r ≠ 0) (hS : ∀ z : K, Valued.v (z - c) ≤ Valued.v r → z ∈ S)
    {g : ↥S → K} (hg : g ∈ holOn K S) :
    ∃ E : Finset K, ∀ (z₀ : K) (hz₀ : Valued.v (z₀ - c) = Valued.v r),
      (∀ e ∈ E, Valued.v r ≤ Valued.v (z₀ - e)) →
        ∀ (z : K) (hz : Valued.v (z - c) ≤ Valued.v r),
          Valued.v (g ⟨z, hS z hz⟩) ≤ Valued.v (g ⟨z₀, hS z₀ hz₀.le⟩) := by sorry

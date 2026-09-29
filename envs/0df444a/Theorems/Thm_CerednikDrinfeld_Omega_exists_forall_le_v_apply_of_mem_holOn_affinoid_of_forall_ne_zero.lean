-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_forall_le_v_apply_of_mem_holOn_affinoid_of_forall_ne_zero
-- name    : CerednikDrinfeld.Omega.exists_forall_le_v_apply_of_mem_holOn_affinoid_of_forall_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/6464e9e6-7b13-55e5-9e3e-5c27ab11e1ac
-- title:
--   Lower bound for zero-free holomorphic functions on Ωₙ
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra which is a field, equipped with a valuation $v$ taking values in a linearly ordered commutative group with zero $\Gamma_0$, and assume $K$ is complete and algebraically closed. Let $\varpi$ be a pseudo-uniformiser of $K_0$ relative to $K$, that is an element $\varpi.\varpi \in K_0$ with $0 < \mathfrak p < 1$ where $\mathfrak p := v(\varpi.\varpi)$ computed in $K$, and such that every nonzero $a \in K_0$ satisfies $\mathfrak p^N \le v(a) \le (\mathfrak p^{-1})^N$ for some $N \in \mathbb N$. Assume the rank-one condition `hrk`: for all $x, y \in K$ with $v(x) < 1$ and $y \ne 0$ there is $n$ with $v(x)^n \le v(y)$. Fix $n \in \mathbb N$ and assume `hfin`: there is a finite set $T \subseteq K_0$ such that every $a \in K_0$ with $v(a) \le (\mathfrak p^{-1})^n$ satisfies $v(a - t) < \mathfrak p^{n}$ for some $t \in T$. Let $S =$ `affinoid` $\varpi\, n$ be the set of $z \in K$ with $v(z) \le (\mathfrak p^{-1})^n$ and $\mathfrak p^{n} \le v(z - a)$ for every $a \in K_0$ with $v(a) \le (\mathfrak p^{-1})^n$. Let $G : S \to K$ lie in the subring `holOn` $K\,S$ of holomorphic functions, i.e. there is a sequence of rational pairs $r_k$, each pole-free on $S$, whose evaluations are uniformly bounded in valuation on $S$ and converge uniformly on $S$ to $G$; assume $G(z) \ne 0$ for every $z \in S$. Then there exists $\delta \in K$, $\delta \ne 0$, with $v(\delta) \le v(G(z))$ for all $z \in S$.
--
--   This is the minimum modulus principle for the affinoids exhausting Drinfeld's upper half plane: a holomorphic function with no zero on the affinoid of level $n$ is bounded below in absolute value, so that its inverse is again bounded and the function is a unit of the ring of holomorphic functions. It is obtained from the corresponding local statement on a residue disc, [`CerednikDrinfeld.Omega.exists_forall_le_v_apply_of_v_sub_lt_of_forall_ne_zero`](thm.html#CerednikDrinfeld.Omega.exists_forall_le_v_apply_of_v_sub_lt_of_forall_ne_zero), and is used in the construction of the ring of holomorphic functions with prescribed invariance and finiteness properties.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_forall_le_v_apply_of_mem_holOn_affinoid_of_forall_ne_zero.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_forall_le_v_apply_of_mem_holOn_affinoid_of_forall_ne_zero
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (n : ℕ)
    (hfin : ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {G : ↥(affinoid ϖ n) → K} (hG : G ∈ holOn K (affinoid ϖ n)) (hG0 : ∀ z : ↥(affinoid ϖ n), G z ≠ 0) :
    ∃ δ : K, δ ≠ 0 ∧ ∀ z : ↥(affinoid ϖ n), Valued.v δ ≤ Valued.v (G z) := by sorry

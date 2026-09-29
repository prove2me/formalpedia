-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_algebraMap_of_isUnit_of_v_apply_eq
-- name    : CerednikDrinfeld.Omega.exists_eq_algebraMap_of_isUnit_of_v_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/f3fe7320-fe89-545f-b07b-3f8b8e3cd85c
-- title:
--   Constant-valuation holomorphic functions on Ω are constant
-- statement:
--   Let $K_0$ be a field and $K$ a $K_0$-algebra which is a field, equipped with a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, and assume $K$ is complete and algebraically closed. Let $\varpi$ be a pseudo-uniformiser: an element $\varpi \in K_0$ with $0 < v(\varpi) < 1$ in $K$ and such that every nonzero $a \in K_0$ satisfies $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N \in \mathbb{N}$. Three further hypotheses are imposed: a rank-one (archimedean) condition, that for all $x, y \in K$ with $v(x) < 1$ and $y \ne 0$ there is $n$ with $v(x)^n \le v(y)$; exhaustion, that every point of the Drinfeld upper half plane $\Omega = K \setminus \operatorname{im}(K_0 \to K)$ lies in one of the affinoids $\{z : v(z) \le v(\varpi)^{-n}$ and $v(z - a) \ge v(\varpi)^n$ for all $a \in K_0$ with $v(a) \le v(\varpi)^{-n}\}$; and a finiteness condition, that for each $n$ there is a finite $T \subseteq K_0$ whose image $v(\varpi)^n$-approximates every $a \in K_0$ with $v(a) \le v(\varpi)^{-n}$. Let $f$ be an element of `holRing ϖ`, the ring of functions $\Omega \to K$ whose restriction to each of these affinoids is, on that affinoid, the uniform limit of a uniformly bounded sequence of rational functions without poles there. Assume $f$ is a unit of that ring and that $v(f(z)) = v(f(w))$ for all $z, w \in \Omega$. Then $f = c$ for some constant $c \in K$, i.e. $f$ is the image of $c$ under the structure map $K \to$ `holRing ϖ`.
--
--   This is the Liouville-type statement that a rigid-holomorphic function on Drinfeld's upper half plane with constant absolute value is constant; in the theory of Mumford curves it expresses the injectivity of van der Put's current map on $\mathcal{O}(\Omega)^\times/K^\times$. It is used in the construction of periods of automorphic theta functions, via [`CerednikDrinfeld.Omega.exists_forall_eq_period_of_isUnit_of_apply_smul_eq_mul_of_forall_isOfFinOrder`](thm.html#CerednikDrinfeld.Omega.exists_forall_eq_period_of_isUnit_of_apply_smul_eq_mul_of_forall_isOfFinOrder).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_exists_eq_algebraMap_of_isUnit_of_v_apply_eq.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.exists_eq_algebraMap_of_isUnit_of_v_apply_eq
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (f : ↥(holRing ϖ)) (hf : IsUnit f)
    (hv : ∀ z w : ↥(upperHalfPlane K₀ K),
      Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) z) = Valued.v ((f : ↥(upperHalfPlane K₀ K) → K) w)) :
    ∃ c : K, f = algebraMap K ↥(holRing ϖ) c := by sorry

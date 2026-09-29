-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_eq_of_sub_pow_mul_eq_of_sub_pow_mul_eq_of_mem_holOn
-- name    : CerednikDrinfeld.Omega.eq_of_sub_pow_mul_eq_of_sub_pow_mul_eq_of_mem_holOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/a7d1fc64-4c54-5ad1-ba35-3fe1b4370703
-- title:
--   Uniqueness of the exponent in a local factorisation (z-p)^e F=φ
-- statement:
--   Let $K$ be a field carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, assumed complete and algebraically closed, and suppose that for all $x,y \in K$ with $v(x) < 1$ and $y \neq 0$ there is $n \in \mathbb{N}$ with $v(x)^n \le v(y)$. Let $S \subseteq K$ be a set, $p \in S$, and $r \neq 0$ an element such that every $z \in K$ with $v(z-p) \le v(r)$ lies in $S$, i.e. $S$ contains the closed disc of radius $v(r)$ about $p$. Let $\pi \neq 0$ satisfy $v(\pi) < 1$. Let $F : S \to K$ be an arbitrary function and let $\varphi, \varphi' : S \to K$ belong to the subring $\mathrm{holOn}\,K\,S$, that is, each is a uniform limit on $S$ of a sequence of rational functions (given as pairs of polynomials) whose denominators have no zero on $S$ and whose values on $S$ are bounded in valuation uniformly in the sequence index. Let $e, e' \in \mathbb{N}$ with $e = 0$ or $\varphi(p) \neq 0$, and $e' = 0$ or $\varphi'(p) \neq 0$, and let $Z \subseteq S$ be finite such that $(z-p)^e F(z) = \varphi(z)$ and $(z-p)^{e'} F(z) = \varphi'(z)$ for all $z \in S \setminus Z$. Then $e = e'$.
--
--   This is the well-definedness of the order of a pole for a function presented locally on a disc as $(z-p)^{-e}\varphi$ with $\varphi$ rigid-analytic and non-vanishing at $p$: two such presentations at the same point, agreeing off a finite set, have the same exponent. It feeds the construction of the ring of chartwise meromorphic functions used in the Cherednik–Drinfeld description of $\Omega$, being cited by [`CerednikDrinfeld.Omega.exists_holRing_forall_finite_mul_eq_of_forall_exists_mem_holOn_affinoid_mul_eq_of_invariant`](thm.html#CerednikDrinfeld.Omega.exists_holRing_forall_finite_mul_eq_of_forall_exists_mem_holOn_affinoid_mul_eq_of_invariant).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_eq_of_sub_pow_mul_eq_of_sub_pow_mul_eq_of_mem_holOn.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.eq_of_sub_pow_mul_eq_of_sub_pow_mul_eq_of_mem_holOn
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    [CompleteSpace K] [IsAlgClosed K]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    {S : Set K} (p : ↥S) (r : K) (hr : r ≠ 0) (hD : ∀ z : K, Valued.v (z - (p : K)) ≤ Valued.v r → z ∈ S)
    (π : K) (hπ0 : π ≠ 0) (hπ : Valued.v π < 1)
    (F : ↥S → K) {φ φ' : ↥S → K} (hφ : φ ∈ holOn K S) (hφ' : φ' ∈ holOn K S)
    {e e' : ℕ} (he : e = 0 ∨ φ p ≠ 0) (he' : e' = 0 ∨ φ' p ≠ 0)
    (Z : Set ↥S) (hZ : Z.Finite)
    (h : ∀ z : ↥S, z ∉ Z → ((z : K) - (p : K)) ^ e * F z = φ z)
    (h' : ∀ z : ↥S, z ∉ Z → ((z : K) - (p : K)) ^ e' * F z = φ' z) :
    e = e' := by sorry

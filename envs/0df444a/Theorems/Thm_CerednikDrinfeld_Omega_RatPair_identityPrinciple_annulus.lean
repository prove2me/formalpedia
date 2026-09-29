-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_RatPair_identityPrinciple_annulus
-- name    : CerednikDrinfeld.Omega.RatPair.identityPrinciple_annulus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/54dcf4ff-be94-5a2d-b745-68de1eb27f85
-- title:
--   Identity principle on an annulus with deleted residue classes
-- statement:
--   Let $K$ be an algebraically closed field equipped with a valuation $v$ taking values in a linearly ordered commutative group with zero. Let $S \subseteq K$, and let $r : \mathbb{N} \to$ `RatPair K` be a sequence of pairs of polynomials $(\mathrm{num}_k, \mathrm{den}_k)$ such that each $\mathrm{den}_k$ has no zero on $S$; write $r_k(z) = \mathrm{num}_k(z)/\mathrm{den}_k(z)$. Let $c, \pi_d, \pi_s \in K$ with $\pi_d \neq 0$, $\pi_s \neq 0$ and $v(\pi_s) < v(\pi_d)$, let $Z$ be a finite subset of $K$ with $v(\pi_d) \le v(c - \zeta)$ for all $\zeta \in Z$, and let $\Xi$ be a finite subset with $v(c - \xi) \le v(\pi_s)$ for all $\xi \in \Xi$. Assume $S$ contains the set $A$ of all $z$ with $v(\pi_s) \le v(z - c) \le v(\pi_d)$, $v(\pi_d) \le v(z - \zeta)$ for every $\zeta \in Z$ and $v(\pi_s) \le v(z - \xi)$ for every $\xi \in \Xi$; assume the sequence is uniformly Cauchy on $S$, in the sense that for every $e \neq 0$ there is $N$ with $v(r_k(z) - r_j(z)) < v(e)$ for all $k, j \ge N$ and all $z \in S$; and assume that $r_k \to 0$ uniformly, in the same $\varepsilon$–$N$ sense with strict inequality $v(r_k(z)) < v(e)$, either on the set of $z$ with $v(z - c) = v(\pi_d)$ and $v(\pi_d) \le v(z - \zeta)$ for all $\zeta \in Z$, or on the set of $z$ with $v(z - c) = v(\pi_s)$ and $v(\pi_s) \le v(z - \xi)$ for all $\xi \in \Xi$. The conclusion is that $r_k \to 0$ uniformly on $A$: for every $e \neq 0$ there is $N$ such that $v(r_k(z)) < v(e)$ for all $k \ge N$ and all $z \in A$.
--
--   This is the identity principle in Laurent (Mittag-Leffler) form for sequences of rational functions on a closed annulus from which finitely many residue classes of the outer and of the inner boundary circle have been removed: uniform vanishing on one of the two boundary circles propagates across the whole annulus. It feeds the vanishing criterion [`CerednikDrinfeld.Omega.eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero`](thm.html#CerednikDrinfeld.Omega.eq_zero_of_mem_holOn_affinoid_of_forall_v_sub_lt_imp_eq_zero) for holomorphic functions on affinoid subsets of the projective line used in the Čerednik–Drinfel'd description of $\Omega$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_RatPair_identityPrinciple_annulus.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.RatPair.identityPrinciple_annulus
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (S : Set K) (r : ℕ → RatPair K) (hr : ∀ k, (r k).IsPoleFreeOn S)
    (c πd πs : K) (hπd : πd ≠ 0) (hπs : πs ≠ 0) (hlt : Valued.v πs < Valued.v πd)
    (Z : Finset K) (hZ : ∀ ζ ∈ Z, Valued.v πd ≤ Valued.v (c - ζ))
    (Ξ : Finset K) (hΞ : ∀ ξ ∈ Ξ, Valued.v (c - ξ) ≤ Valued.v πs)
    (hS : ∀ z : K, Valued.v πs ≤ Valued.v (z - c) → Valued.v (z - c) ≤ Valued.v πd →
      (∀ ζ ∈ Z, Valued.v πd ≤ Valued.v (z - ζ)) → (∀ ξ ∈ Ξ, Valued.v πs ≤ Valued.v (z - ξ)) → z ∈ S)
    (hC : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ z ∈ S,
      Valued.v ((r k).evalAt z - (r j).evalAt z) < Valued.v e)
    (h0 : (∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z : K, Valued.v (z - c) = Valued.v πd →
            (∀ ζ ∈ Z, Valued.v πd ≤ Valued.v (z - ζ)) → Valued.v ((r k).evalAt z) < Valued.v e) ∨
          (∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z : K, Valued.v (z - c) = Valued.v πs →
            (∀ ξ ∈ Ξ, Valued.v πs ≤ Valued.v (z - ξ)) → Valued.v ((r k).evalAt z) < Valued.v e)) :
    ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z : K, Valued.v πs ≤ Valued.v (z - c) → Valued.v (z - c) ≤ Valued.v πd →
      (∀ ζ ∈ Z, Valued.v πd ≤ Valued.v (z - ζ)) → (∀ ξ ∈ Ξ, Valued.v πs ≤ Valued.v (z - ξ)) →
      Valued.v ((r k).evalAt z) < Valued.v e := by sorry

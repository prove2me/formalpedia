-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_RatPair_identityPrinciple_disc
-- name    : CerednikDrinfeld.Omega.RatPair.identityPrinciple_disc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/e8384be1-2277-5947-a3c2-51d72dd4654b
-- title:
--   Identity principle on a disc minus residue classes
-- statement:
--   Let $K$ be an algebraically closed field carrying a valuation $v$ with values in a linearly ordered commutative group with zero, and let $S \subseteq K$. Let $(r_k)_{k \in \mathbb{N}}$ be a sequence of pairs of polynomials over $K$, written as a numerator and a denominator, such that for each $k$ the denominator of $r_k$ does not vanish at any point of $S$; the value $(r_k).\mathrm{evalAt}(z)$ is the quotient of the two polynomial values at $z$. Let $c, \pi \in K$ with $\pi \neq 0$, and let $Z \subseteq K$ be a finite set such that $v(\pi) \le v(c - \zeta)$ for every $\zeta \in Z$. Assume that $S$ contains the set $F$ of all $z \in K$ with $v(z - c) \le v(\pi)$ and $v(\pi) \le v(z - \zeta)$ for all $\zeta \in Z$. Assume further that $(r_k)$ is uniformly Cauchy on $S$: for every $e \neq 0$ there is $N$ with $v(r_k(z) - r_j(z)) < v(e)$ for all $k, j \ge N$ and all $z \in S$. Finally let $\delta \neq 0$ and assume $(r_k)$ tends to $0$ uniformly on $\{z \in S : v(z - c) \le v(\delta)\}$, in the sense that for every $e \neq 0$ there is $N$ with $v(r_k(z)) < v(e)$ for all $k \ge N$ and all such $z$. The conclusion is that $(r_k)$ tends to $0$ uniformly on $F$: for every $e \neq 0$ there is $N$ such that for all $k \ge N$ and every $z \in K$ with $v(z - c) \le v(\pi)$ and $v(\pi) \le v(z - \zeta)$ for all $\zeta \in Z$, one has $v(r_k(z)) < v(e)$.
--
--   This is the identity principle, in sequence form, for the affinoid $F$ obtained from a closed disc by deleting finitely many open residue classes of full radius (the class of the centre $c$ being retained): uniform vanishing near the centre propagates to all of $F$. Phrased for explicitly presented quotients of polynomials and uniformly Cauchy sequences rather than for limit functions, it requires neither completeness of $K$ nor a value group of rank one; it is used for the corresponding statement on annuli, for a bound on differences of pole-free rational functions on an affinoid, and for the vanishing of holomorphic functions on vertex affinoids in the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_RatPair_identityPrinciple_disc.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.RatPair.identityPrinciple_disc
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (S : Set K) (r : ℕ → RatPair K) (hr : ∀ k, (r k).IsPoleFreeOn S)
    (c π : K) (hπ : π ≠ 0) (Z : Finset K) (hZ : ∀ ζ ∈ Z, Valued.v π ≤ Valued.v (c - ζ))
    (hS : ∀ z : K, Valued.v (z - c) ≤ Valued.v π → (∀ ζ ∈ Z, Valued.v π ≤ Valued.v (z - ζ)) → z ∈ S)
    (hC : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ j ≥ N, ∀ z ∈ S,
      Valued.v ((r k).evalAt z - (r j).evalAt z) < Valued.v e)
    (δ : K) (hδ : δ ≠ 0)
    (h0 : ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z ∈ S, Valued.v (z - c) ≤ Valued.v δ →
      Valued.v ((r k).evalAt z) < Valued.v e) :
    ∀ e : K, e ≠ 0 → ∃ N : ℕ, ∀ k ≥ N, ∀ z : K, Valued.v (z - c) ≤ Valued.v π →
      (∀ ζ ∈ Z, Valued.v π ≤ Valued.v (z - ζ)) → Valued.v ((r k).evalAt z) < Valued.v e := by sorry

-- Prove2me | Theorems.Thm_DerivativeChainContinuation_coordinate_chain_collision_limit_with_fixed_start
-- name    : DerivativeChainContinuation.coordinate_chain_collision_limit_with_fixed_start
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T02:40:42.026777+00:00
-- url     : https://prove2.me/theorems/0c63d39b-ebb7-45a3-a0d2-a547f6446e18
-- title:
--   Fixed-start coordinate chains survive coefficient limits
-- statement:
--   Fix $N>0$, a tail index $k$, a reference index $\ell<N$, and $\eta\in\mathbb C$. Let polynomials $p_j$ and $q$ have degree at most $N$, with every coefficient of $p_j$ converging to that of $q$. Suppose uniformly bounded lists $z^{(j)}\in\mathbb C^N$ satisfy $p_j^{(N-i-1)}(z_i^{(j)})=0$, start at $\eta$, have nondecreasing real and imaginary coordinates, and satisfy $z_i^{(j)}=z_\ell^{(j)}$ for $i\ge k$. There is a list $w$ with these same root, start, tail, and monotonicity properties for $q$. The degree bound need not be an equality.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/higher_powers/Source/CoordinateLimits.lean#L8-L52

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainContinuation.coordinate_chain_collision_limit_with_fixed_start (n k : ℕ) [NeZero n] (last : Fin n)
    (p : ℕ → Polynomial ℂ) (q : Polynomial ℂ)
    (hp : ∀ j, (p j).natDegree ≤ n) (hq : q.natDegree ≤ n)
    (hc : ∀ k, Tendsto (fun j => (p j).coeff k) atTop (𝓝 (q.coeff k)))
    (z : ℕ → Fin n → ℂ) (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ j i, ‖z j i‖ ≤ M)
    (hroot : ∀ j i, (Polynomial.derivative^[n-(i.val+1)] (p j)).eval (z j i)=0)
    (η : ℂ) (hstart : ∀ j, z j 0=η)
    (htail : ∀ j i, k ≤ i.val → z j i=z j last)
    (hmonoR : ∀ j, Monotone (fun i => (z j i).re))
    (hmonoI : ∀ j, Monotone (fun i => (z j i).im)) :
    ∃ w : Fin n → ℂ,
      (∀ i, (Polynomial.derivative^[n-(i.val+1)] q).eval (w i)=0) ∧
      w 0=η ∧ (∀ i : Fin n, k ≤ i.val → w i=w last) ∧
      Monotone (fun i => (w i).re) ∧ Monotone (fun i => (w i).im) := by sorry

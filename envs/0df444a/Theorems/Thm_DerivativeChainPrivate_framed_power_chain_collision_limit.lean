-- Prove2me | Theorems.Thm_DerivativeChainPrivate_framed_power_chain_collision_limit
-- name    : DerivativeChainPrivate.framed_power_chain_collision_limit
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T03:07:15.100199+00:00
-- url     : https://prove2.me/theorems/f487fc49-9675-4d51-9a3e-7c8484dab8f7
-- title:
--   Fixed-start chains and their frames survive coefficient limits
-- statement:
--   For a finite complex list $z_0,\ldots,z_{N-1}$ write $L(z)=\sum_{i=0}^{N-2}|z_{i+1}-z_i|$. Fix $N>0$, a tail index $k$, reference index $\ell<N$, and start $\eta$. Let degree-at-most-$N$ polynomials $p_j$ converge coefficientwise to such a polynomial $q$. Suppose uniformly bounded lists $z^{(j)}\in\mathbb C^N$ lie in the roots of $p_j^{(N-i-1)}$, start at $\eta$, and are constant from $k$ to the chosen reference entry. Assume each list admits unit orthogonal coefficients $a_j,b_j$ with nondecreasing projections, and $L(z^{(j)})\le c_j\to C$. There is a corresponding root list for $q$ with the same start and tail, unit orthogonal frames, monotone projections, and length at most $C$. Degree equality with $N$ is not assumed.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/higher_powers/Source/FrameLimits.lean#L8-L94

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.framed_power_chain_collision_limit (n k : ℕ) [NeZero n] (last : Fin n) (p : ℕ → Polynomial ℂ) (q : Polynomial ℂ)
    (hp : ∀ j, (p j).natDegree ≤ n) (hq : q.natDegree ≤ n)
    (hc : ∀ k, Tendsto (fun j => (p j).coeff k) atTop (𝓝 (q.coeff k)))
    (z : ℕ → Fin n → ℂ) (a b : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j i, ‖z j i‖ ≤ M)
    (hroot : ∀ j i, (Polynomial.derivative^[n-(i.val+1)] (p j)).eval (z j i) = 0)
    (η : ℂ) (hstart : ∀ j, z j 0 = η)
    (htail : ∀ j i, k ≤ i.val → z j i = z j last)
    (ha : ∀ j, ‖a j‖ = 1) (hb : ∀ j, ‖b j‖ = 1)
    (hab : ∀ j, (a j*starRingEnd ℂ (b j)).re = 0)
    (hmonoA : ∀ j, Monotone (fun i => (a j*z j i).re))
    (hmonoB : ∀ j, Monotone (fun i => (b j*z j i).re))
    (c : ℕ → ℝ) (C : ℝ) (hcLim : Tendsto c atTop (𝓝 C))
    (hcost : ∀ j, chainCost (z j) ≤ c j) :
    ∃ (w : Fin n → ℂ) (A B : ℂ),
      (∀ i, (Polynomial.derivative^[n-(i.val+1)] q).eval (w i) = 0) ∧
      w 0 = η ∧ (∀ i : Fin n, k ≤ i.val → w i = w last) ∧
      ‖A‖ = 1 ∧ ‖B‖ = 1 ∧ (A*starRingEnd ℂ B).re = 0 ∧
      Monotone (fun i => (A*w i).re) ∧ Monotone (fun i => (B*w i).re) ∧ chainCost w ≤ C := by sorry

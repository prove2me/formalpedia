-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_NonemptyCut_capacity_normalization
-- name    : DecrAlmostLinearSSSP.Decremental.NonemptyCut.capacity_normalization
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:20:23.183401+00:00
-- url     : https://prove2.me/theorems/85555c12-8b8d-4bb7-9c82-e7073937bba2
-- title:
--   Uniform capacity normalization for the dynamic-cut wrapper
-- statement:
--   Let $M=\max\{2,m\}$ and $S=M^d$, where $d$ is the fixed numerical-range exponent. Starting with a valid physical instance whose active capacities lie in $[M^{-d},M^d]$, form $\widehat g$ by multiplying every capacity by $S$, without changing endpoints, active identifiers, or demands. If the supplied initialization bound $B$ is positive, at most $M^d$, and covers all active capacities, then $\widehat g$ has the same size, zero-sum demand, and connected-kernel properties and satisfies
--
--   $$
--   1\le \widehat u_e\le M^{2d},\qquad
--   0<SB\le M^{2d},\qquad
--   \widehat u_e\le SB
--   $$
--
--   on active edges. The vertex demands retain their original bound $|\gamma_v|\le M^d$. This is the numerical normalization used to invoke the dynamic-cut implementation of Lemma 3.2, including its initialization capacity bound.
--
--   **Formalization Note** The normalized range conditions are written out using `Physical`, so this theorem does not introduce or depend on a separate normalized-validity definition.
-- source:
--   Cui, Li, Miao and Wang, Partially Dynamic Single-Source Shortest Paths in Almost-Linear Time, STOC 2027 submission #912, p. 9, Lemma 3.2 and equation (3.12); polynomial numerical-range implementation convention for the dynamic-cut wrapper; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf.

import Definitions.Def_DecrAlmostLinearSSSP_NonemptyCutProtocol

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal

/-- Scale capacities to `[1, M^(2d)]`, including the supplied initialization bound. -/
theorem DecrAlmostLinearSSSP.Decremental.NonemptyCut.capacity_normalization {n k : ℕ}
    (g : Physical n k) (m exponent : ℕ)
    (capacityBound : ℝ) (hg : g.Valid m exponent)
    (hB0 : 0 < capacityBound) (hB : capacityBound ≤ (max 2 m : ℝ) ^ exponent)
    (huB : ∀ e ∈ g.active, g.u e ≤ capacityBound) :
    let S : ℝ := (max 2 m : ℝ) ^ exponent
    let ĝ : Physical n k := { g with u := fun e => S * g.u e }
    (n ≤ m ∧ k ≤ m ∧ 0 < n ∧
      (∀ e ∈ ĝ.active, 1 ≤ ĝ.u e ∧ ĝ.u e ≤ (max 2 m : ℝ) ^ (2 * exponent)) ∧
      (∑ v, ĝ.gamma v) = 0 ∧ (∀ v, |ĝ.gamma v| ≤ (max 2 m : ℝ) ^ exponent) ∧
      (∀ x, physicalNorm ĝ x = 0 → ∀ v w, x v = x w)) ∧
    0 < S * capacityBound ∧ S * capacityBound ≤ (max 2 m : ℝ) ^ (2 * exponent) ∧
    ∀ e ∈ ĝ.active, ĝ.u e ≤ S * capacityBound := by sorry

-- Prove2me | Theorems.Thm_DerivativeChainPrivate_coordinate_chain_collision_limit
-- name    : DerivativeChainPrivate.coordinate_chain_collision_limit
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:18:14.730312+00:00
-- url     : https://prove2.me/theorems/8bb8ed58-71cd-457f-9e81-83ff771e6056
-- title:
--   Coordinate monotonicity and fixed suffixes survive polynomial limits
-- statement:
--   For a fixed finite list of derivative orders, consider uniformly bounded lists of zeros of those iterated derivatives for coefficientwise-convergent polynomials with a common degree upper bound. A limiting list of derivative zeros retains convergent cost upper bounds, monotonicity of both coordinates and an eventually constant final suffix. Degree equality with the list length is not assumed, so this lemma alone does not assert a complete nonconstant-row tower or construct chains for arbitrary families.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/cube_continuation/Source/CoherentLimits.lean#L7-L62

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
namespace DerivativeChainPrivate
end DerivativeChainPrivate
open DerivativeChainPrivate Filter Topology Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem DerivativeChainPrivate.coordinate_chain_collision_limit {n N : ℕ}
    (p : ℕ → Polynomial ℂ) (q : Polynomial ℂ)
    (hp : ∀ j, (p j).natDegree ≤ N) (hq : q.natDegree ≤ N)
    (hc : ∀ k, Tendsto (fun j => (p j).coeff k) atTop (𝓝 (q.coeff k)))
    (z : ℕ → Fin n → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hzbound : ∀ j i, ‖z j i‖ ≤ R)
    (hzroot : ∀ j i, (Polynomial.derivative^[n - (i.val + 1)] (p j)).eval (z j i) = 0)
    (c : ℕ → ℝ) (C : ℝ) (hcLim : Tendsto c atTop (𝓝 C))
    (hcost : ∀ j, chainCost (z j) ≤ c j)
    (hre : ∀ j, Monotone (fun i => (z j i).re))
    (him : ∀ j, Monotone (fun i => (z j i).im))
    (k : ℕ) (last : Fin n) (htail : ∀ j i, k ≤ i.val → z j i = z j last) :
    ∃ w : Fin n → ℂ,
      (∀ i, (Polynomial.derivative^[n - (i.val + 1)] q).eval (w i) = 0) ∧
      chainCost w ≤ C ∧ Monotone (fun i => (w i).re) ∧
      Monotone (fun i => (w i).im) ∧ (∀ i, k ≤ i.val → w i = w last) := by sorry

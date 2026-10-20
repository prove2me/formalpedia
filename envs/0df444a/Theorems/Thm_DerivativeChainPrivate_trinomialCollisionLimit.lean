-- Prove2me | Theorems.Thm_DerivativeChainPrivate_trinomialCollisionLimit
-- name    : DerivativeChainPrivate.trinomialCollisionLimit
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-18T07:42:50.29161+00:00
-- url     : https://prove2.me/theorems/c027bc00-9213-479e-a8e4-8e55a4873384
-- title:
--   Bounded derivative-root chains survive coefficient limits and collisions
-- statement:
--   For a fixed positive degree n, coefficientwise-convergent complex polynomials of degree n and uniformly bounded complete derivative-root chains admit a subsequential limiting complete chain. If the cost bounds converge to C, the limiting chain has cost at most C. Root collisions and multiplicities are allowed.
-- source:
--   Derivative-zero chains: public formalization reference, R42, DerivativeChainPrivate.trinomialCollisionLimit. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Definitions.Def_DerivativeChainPrivate_foundations
open Filter Topology
open scoped BigOperators
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem DerivativeChainPrivate.trinomialCollisionLimit {n : ℕ} (_hn : 0 < n)
    (p : ℕ → Polynomial ℂ) (q : Polynomial ℂ)
    (hp : ∀ j, (p j).natDegree = n) (hq : q.natDegree = n)
    (hc : ∀ k, Tendsto (fun j => (p j).coeff k) atTop (𝓝 (q.coeff k)))
    (z : ℕ → Fin n → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hzbound : ∀ j i, ‖z j i‖ ≤ R)
    (hzroot : ∀ j i, (Polynomial.derivative^[n - (i.val + 1)] (p j)).eval (z j i) = 0)
    (c : ℕ → ℝ) (C : ℝ) (hcLim : Tendsto c atTop (𝓝 C))
    (hcost : ∀ j, chainCost (z j) ≤ c j) :
    ∃ w : Fin n → ℂ,
      (∀ i, (Polynomial.derivative^[n - (i.val + 1)] q).eval (w i) = 0) ∧ chainCost w ≤ C := by sorry

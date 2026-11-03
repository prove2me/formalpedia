-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_int_forall_mem_Ioo_of_forall_ne
-- name    : FiniteEnergyPlane.exists_int_forall_mem_Ioo_of_forall_ne
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-02T16:00:34.260113+00:00
-- url     : https://prove2.me/theorems/58877060-215e-461c-982d-1d6c438a90c5
-- title:
--   A continuous real function avoiding a coset of a lattice stays in one period window
-- statement:
--   Let $X$ be a nonempty preconnected topological space, let $f:X\to\mathbb{R}$ be continuous, and let $c\in\mathbb{R}$ and $L>0$. If $f(x)\neq c+mL$ for every $x\in X$ and every $m\in\mathbb{Z}$, then there is $m\in\mathbb{Z}$ with
--   $$c+mL<f(x)<c+(m+1)L\quad\text{for all }x\in X.$$
--
--   This confines continuous angle functions, such as lifts of arguments, to a single window of one period.
-- source:
--   Auxiliary lemma for J. Gutt, Ann. Fac. Sci. Toulouse Math. 23 (2014), arXiv:1307.7239, Section 2, and U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.1.1

import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Order.Floor.Ring

namespace FiniteEnergyPlane

/-- A continuous real function on a nonempty preconnected space that never takes a value in the
coset `c + Lℤ` (`L > 0`) takes all its values in a single interval `(c + mL, c + (m + 1)L)`. -/
theorem exists_int_forall_mem_Ioo_of_forall_ne {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] [Nonempty X] (f : X → ℝ) (hf : Continuous f) (c L : ℝ) (hL : 0 < L)
    (h : ∀ x, ∀ m : ℤ, f x ≠ c + m * L) :
    ∃ m : ℤ, ∀ x, c + m * L < f x ∧ f x < c + (m + 1) * L := by
  sorry

end FiniteEnergyPlane

-- Prove2me | Theorems.Thm_BregmanPPA_Convergence_theorem1
-- name    : BregmanPPA.Convergence.theorem1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:22:40.005996+00:00
-- url     : https://prove2.me/theorems/f4b59a99-4af1-487f-89e4-c073bce4a494
-- title:
--   Theorem 1 — convergence or unboundedness of the Bregman proximal-point run
-- statement:
--   Let $T$ be maximal monotone on a finite-dimensional real inner-product space. Let $h$ be a Bregman function with zone $S$, with $\operatorname{dom}T\subseteq\overline S$. Let $(c_k)$ be positive and bounded below by a positive constant, and let $(x^k)$ be an infinite Bregman proximal-point run. Assume either (C1) $\overline{\operatorname{dom}T}\subseteq S$, or (C2) $T=\partial f$ for a proper lower semicontinuous convex function $f$. Then:
--
--   $$\begin{aligned}
--   T^{-1}(0)\ne\varnothing&\quad\Longrightarrow\quad x^k\to z\text{ for some }z\in T^{-1}(0),\\
--   T^{-1}(0)=\varnothing\ \text{and (C1)}&\quad\Longrightarrow\quad \{x^k:k\ge0\}\text{ is unbounded}.
--   \end{aligned}$$
--
--   This is the paper's central convergence and divergence alternative for nonlinear proximal-point algorithms.
--
--   **Formalization Note** The space is a finite-dimensional real inner-product space, representing $\mathbb R^n$. The run explicitly keeps every iterate in $S$ and expresses (3) through the equivalent inclusion (4). The standing inclusion $\operatorname{dom}T\subseteq\overline S$ differs from (C1), $\overline{\operatorname{dom}T}\subseteq S$. Unbounded means the range of the full sequence is not bounded.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), pp. 206–207, Theorem 1, https://doi.org/10.1287/moor.18.1.202

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model

open ThreeOpSplitting.Convergence InertialFB.IFB Filter Topology

namespace BregmanPPA.Convergence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- Theorem 1: convergence to a zero, or unboundedness when there are no zeros under (C1). -/
theorem theorem1 (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMaximalMonotone T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hx : IsBregmanPPARun S h T c x)
    (hC : closure (dom T) ⊆ S ∨ ∃ f : H → EReal,
      IsProperFn f ∧ IsConvexFn f ∧ LowerSemicontinuous f ∧ T = subdiffOp f) :
    ((zer T).Nonempty → ∃ z : H, z ∈ zer T ∧ Tendsto x atTop (𝓝 z)) ∧
    (zer T = ∅ → closure (dom T) ⊆ S → ¬ Bornology.IsBounded (Set.range x)) := by sorry

end BregmanPPA.Convergence

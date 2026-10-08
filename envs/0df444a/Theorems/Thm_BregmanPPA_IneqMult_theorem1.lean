-- Prove2me | Theorems.Thm_BregmanPPA_IneqMult_theorem1
-- name    : BregmanPPA.IneqMult.theorem1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:19:07.390989+00:00
-- url     : https://prove2.me/theorems/a631700d-ced3-4949-8093-47fe9733ed50
-- title:
--   Theorem 1 — convergence or unboundedness of a Bregman proximal-point run
-- statement:
--   Let $T$ be maximal monotone on a finite-dimensional real inner-product space, let $h$ be a Bregman function with zone $S$ such that $\operatorname{dom}T\subseteq\overline S$, and let $(x^k)$ obey the Bregman proximal-point recursion with positive step sizes bounded below by a positive constant. Suppose either (C1) $\overline{\operatorname{dom}T}\subseteq S$, or (C2) $T=\partial f$ for a proper lower semicontinuous convex function $f$. Then
--
--   $$T^{-1}(0)\ne\varnothing\ \Longrightarrow\ x^k\to z\in T^{-1}(0),\qquad T^{-1}(0)=\varnothing\text{ and (C1)}\ \Longrightarrow\ \{x^k\}\text{ is unbounded}.$$
--
--   This theorem supplies the convergence alternative used for the negative dual subdifferential in Theorem 7.
--
--   **Formalization Note** The standing inclusion $\operatorname{dom}T\subseteq\overline S$ is distinct from condition (C1). The run is equation (4), equivalent to (3), and explicitly keeps iterates in $S$.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), pp. 206–207, Theorem 1, https://doi.org/10.1287/moor.18.1.202

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model

open Filter Topology ThreeOpSplitting.Convergence InertialFB.IFB

namespace BregmanPPA.IneqMult

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- Theorem 1, pp. 206–207, restated for use with the inequality dual operator. -/
theorem theorem1 (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMaximalMonotone T) (hh : BregmanPPA.Convergence.IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hx : BregmanPPA.Convergence.IsBregmanPPARun S h T c x)
    (hC : closure (dom T) ⊆ S ∨ ∃ f : H → EReal,
      IsProperFn f ∧ IsConvexFn f ∧ LowerSemicontinuous f ∧ T = BregmanPPA.Convergence.subdiffOp f) :
    ((zer T).Nonempty → ∃ z : H, z ∈ zer T ∧ Tendsto x atTop (𝓝 z)) ∧
    (zer T = ∅ → closure (dom T) ⊆ S → ¬ Bornology.IsBounded (Set.range x)) := by sorry

end BregmanPPA.IneqMult

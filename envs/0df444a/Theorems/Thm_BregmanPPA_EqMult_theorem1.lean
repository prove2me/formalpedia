-- Prove2me | Theorems.Thm_BregmanPPA_EqMult_theorem1
-- name    : BregmanPPA.EqMult.theorem1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:18:13.603915+00:00
-- url     : https://prove2.me/theorems/8a52a98d-3493-4e99-bb04-e956da954c2b
-- title:
--   Theorem 1 — the Bregman proximal point algorithm converges to a zero of a maximal monotone operator
-- statement:
--   Let $H$ be a finite-dimensional real inner product space, $T : H \to 2^H$ a maximal monotone operator, and $h$ a Bregman function with zone $S$ such that $\bar S \supseteq \operatorname{dom} T$. Let $\{c_k\}_{k\ge0}$ be positive scalars with $\inf_k c_k > 0$, and let $\{x^k\}_{k\ge 0}$ be an infinite sequence conforming to the recursion
--   $$x^{k+1} = (\nabla h + c_k T)^{-1}\bigl(\nabla h(x^k)\bigr). \tag{3}$$
--   Suppose that one of the following holds:
--
--   1. (C1) $S \supseteq \overline{\operatorname{dom} T}$;
--   2. (C2) $T = \partial f$ for a proper lower semicontinuous convex function $f : H \to (-\infty,+\infty]$.
--
--   Then, if $T$ has a zero, $\{x^k\}$ converges to a zero of $T$. If $T$ has no zero and (C1) holds, then $\{x^k\}$ is unbounded.
--
--   This is the central convergence theorem of the paper. In §4.1 it is applied to $T = \partial(-d)$, the subdifferential of the negated dual functional of an equality-constrained convex program, for which (C2) holds.
--
--   **Formalization Note** The paper prints "maximal monontone operator of $\mathbb R^n$"; it means a maximal monotone operator on $\mathbb R^n$, here a finite-dimensional real inner product space $H$. A run of (3) is encoded through the paper's equivalent form (4) together with $x^k \in S$. "Converges to one of them" is $\exists z,\ 0 \in T z \wedge x^k \to z$; "unbounded" is "the range of $k \mapsto x^k$ is not bounded". $\inf c_k > 0$ is "$\exists \varepsilon > 0,\ \varepsilon \le c_k$ for all $k$". This restates the goal of mission 1 of this series in this mission's namespace.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), pp. 206–207, Theorem 1

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_BregmanPPA_Convergence_Model

open ThreeOpSplitting.Convergence InertialFB.IFB Filter Topology

namespace BregmanPPA.EqMult
theorem theorem1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMaximalMonotone T) (hh : BregmanPPA.Convergence.IsBregmanFunction S h) (hdom : dom T ⊆ closure S)
    (hc : ∀ k, 0 < c k) (hcinf : ∃ ε > 0, ∀ k, ε ≤ c k)
    (hx : BregmanPPA.Convergence.IsBregmanPPARun S h T c x)
    (hC : closure (dom T) ⊆ S ∨
      ∃ f : H → EReal, IsProperFn f ∧ IsConvexFn f ∧ LowerSemicontinuous f ∧ T = BregmanPPA.Convergence.subdiffOp f) :
    ((zer T).Nonempty → ∃ z ∈ zer T, Tendsto x atTop (𝓝 z)) ∧
    (zer T = ∅ → closure (dom T) ⊆ S → ¬ Bornology.IsBounded (Set.range x)) := by sorry
end BregmanPPA.EqMult

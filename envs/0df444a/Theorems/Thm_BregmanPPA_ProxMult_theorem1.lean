-- Prove2me | Theorems.Thm_BregmanPPA_ProxMult_theorem1
-- name    : BregmanPPA.ProxMult.theorem1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:13:53.656024+00:00
-- url     : https://prove2.me/theorems/eb64c586-e7c6-406f-bfde-32da57e90792
-- title:
--   Theorem 1 — the Bregman proximal point algorithm converges to a zero of a maximal monotone T
-- statement:
--   Let $H$ be a finite-dimensional real inner product space, $T:H\rightrightarrows H$ a maximal monotone operator, and $h$ a Bregman function with zone $S$, $\overline S\supseteq\operatorname{dom}T$. Let $\{c_k\}$ be positive scalars with $\inf_k c_k>0$, and let $\{x^k\}$ be an infinite sequence conforming to
--
--   $$x^{k+1}=(\nabla h+c_kT)^{-1}\big(\nabla h(x^k)\big).\tag{3}$$
--
--   Suppose that (C1) $S\supseteq\overline{\operatorname{dom}T}$, or (C2) $T=\partial f$ for a proper lower semicontinuous convex $f:H\to(-\infty,+\infty]$. Then if $T$ has a zero, $\{x^k\}$ converges to one of them. If $T$ has no zero and (C1) holds, $\{x^k\}$ is unbounded.
--
--   This is the paper's central theorem, restated in this mission so that it can be applied to the saddle operator $K$ on $\mathbb R^{n+m}$.
--
--   **Formalization Note** The paper states the theorem on $\mathbb R^n$ (and prints "maximal monontone operator of $\mathbb R^n$"); the restatement is over any finite-dimensional real inner product space, which is $\mathbb R^n$ up to isometry and includes $\mathbb R^{n+m}$ as `WithLp 2 (E n × E m)`. (3) is encoded by (4) with $x^k\in S$. "Converges to one of them" is $\exists z,\ 0\in T z\wedge x^k\to z$; "unbounded" is "the range of $x$ is not bounded".
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), pp. 206–207, Theorem 1

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model

open Filter Topology ThreeOpSplitting.Convergence InertialFB.IFB

namespace BregmanPPA.ProxMult

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- Theorem 1, pp. 206–207, restated on a finite-dimensional inner product space `H` (it is
applied on `ℝⁿ⁺ᵐ`): convergence to a zero, or unboundedness when there is none under (C1). -/
theorem theorem1 (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMaximalMonotone T) (hh : BregmanPPA.Convergence.IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hx : BregmanPPA.Convergence.IsBregmanPPARun S h T c x)
    (hC : closure (dom T) ⊆ S ∨ ∃ f : H → EReal,
      IsProperFn f ∧ IsConvexFn f ∧ LowerSemicontinuous f ∧ T = BregmanPPA.Convergence.subdiffOp f) :
    ((zer T).Nonempty → ∃ z : H, z ∈ zer T ∧ Tendsto x atTop (𝓝 z)) ∧
    (zer T = ∅ → closure (dom T) ⊆ S → ¬ Bornology.IsBounded (Set.range x)) := by sorry

end BregmanPPA.ProxMult

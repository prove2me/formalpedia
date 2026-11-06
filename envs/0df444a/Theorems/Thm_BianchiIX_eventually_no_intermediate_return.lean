-- Prove2me | Theorems.Thm_BianchiIX_eventually_no_intermediate_return
-- name    : BianchiIX.eventually_no_intermediate_return
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T22:45:52.397372+00:00
-- url     : https://prove2.me/theorems/cc90d113-c6e4-4fbf-8464-2ab4afda0fd5
-- title:
--   Persistence of the absence of intermediate returns
-- statement:
--   Let $X$ be a topological space, $x_0\in X$,
--   $T:X\to\mathbb R$ be continuous at $x_0$ with $T(x_0)>0$, and
--   $g:X\times\mathbb R\to\mathbb R$. Fix $c\in\mathbb R$.
--   Assume that $g(x,t)=c$ implies $t=0$ near $(x_0,0)$ and implies
--   $t=T(x)$ near $(x_0,T(x_0))$. Suppose $g$ is continuous at every
--   $(x_0,t)$ with $0<t<T(x_0)$ and $g(x_0,t)\ne c$ there.
--   Then for all $x$ sufficiently near $x_0$,
--   $$g(x,t)\ne c\quad(0<t<T(x)).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/FirstReturnPersistence.lean#L35-L59

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
variable {X : Type*} [TopologicalSpace X]

theorem BianchiIX.eventually_no_intermediate_return {x₀ : X} {T : X → ℝ}
    {g : X → ℝ → ℝ} {c : ℝ} (hT : ContinuousAt T x₀) (hpos : 0 < T x₀)
    (hentry : ∀ᶠ z : X × ℝ in 𝓝 (x₀, 0), g z.1 z.2 = c → z.2 = 0)
    (hexit : ∀ᶠ z : X × ℝ in 𝓝 (x₀, T x₀), g z.1 z.2 = c → z.2 = T z.1)
    (hcont : ∀ t ∈ Ioo 0 (T x₀), ContinuousAt (fun z : X × ℝ => g z.1 z.2) (x₀, t))
    (havoid : ∀ t ∈ Ioo 0 (T x₀), g x₀ t ≠ c) :
    ∀ᶠ x in 𝓝 x₀, ∀ t ∈ Ioo 0 (T x), g x t ≠ c := by sorry

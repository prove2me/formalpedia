-- Prove2me | Theorems.Thm_ClarkeStrat_KL_proposition_10
-- name    : ClarkeStrat.KL.proposition_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:30.206377+00:00
-- url     : https://prove2.me/theorems/bc7fbe15-da82-4fd6-bd1a-c5beb3df059c
-- title:
--   Proposition 10 (uniform boundedness), p. 565 — a definable ψ dominating φ(·, s) uniformly in s ∈ [a, +∞)
-- statement:
--   Let $\mathcal O$ be an o-minimal structure, $a\in\mathbb R$ and $I=[a,+\infty)$. Let $\mathcal V\subseteq\mathbb R_+\times I$ be a definable set which is a neighbourhood of $\{0\}\times I$ relative to $\mathbb R_+\times I$, and let $\phi:\mathcal V\to\mathbb R_+$ be a definable function, continuous (relative to $\mathcal V$) at every point of $\{0\}\times I$, with $\phi(0,s)=0$ for all $s\in I$. Then there exist $\varepsilon_0>0$, a continuous definable function $\chi:I\to(0,\varepsilon_0)$ and a continuous definable function $\psi:[0,\varepsilon_0)\to[0,+\infty)$ which is $C^1$ on $(0,\varepsilon_0)$, with $\psi(0)=0$, such that $(t,s)\in\mathcal V$ and
--   $$\psi(t)\ge\phi(t,s)\qquad\text{for all } s\in I,\ t\in(0,\chi(s)).$$
--
--   This uniform bound is the tool that extends the Kurdyka–Łojasiewicz inequality to unbounded domains (Theorem 11).
--
--   **Formalization Note** The paper prints $\psi:(0,\varepsilon_0)\to[0,+\infty)$ while asserting $\psi(0)=0$; its proof defines $\psi$ on $[0,\varepsilon_0)$ and shows continuity at $0$, which is what is stated. Since $\phi$ is only defined on $\mathcal V$, the conclusion states explicitly that $(t,s)\in\mathcal V$. $\phi$ is a function of two real variables whose values outside $\mathcal V$ are irrelevant.
-- source:
--   Bolte, Daniilidis, Lewis & Shiota, Clarke subgradients of stratifiable functions, SIAM J. Optim. 18(2) (2007), p. 565, Proposition 10

import Mathlib
import Definitions.Def_ClarkeStrat_KL_Setting

open Filter Topology
open scoped Pointwise InnerProductSpace
open NonconvexSplitting.Shared

namespace ClarkeStrat.KL

/-- Proposition 10 (uniform boundedness), p. 565. Let `I = [a, +∞)`, let `𝒱 ⊆ ℝ₊ × I` be a definable
neighbourhood of `{0} × I` in `ℝ₊ × I`, and let `φ : 𝒱 → ℝ₊` be definable, continuous at the points
of `{0} × I`, with `φ(0, s) = 0` for `s ∈ I`. Then there are `ε₀ > 0`, a continuous definable
`χ : I → (0, ε₀)` and a continuous definable `ψ : [0, ε₀) → [0, +∞)`, `C¹` on `(0, ε₀)` with
`ψ(0) = 0`, such that `(t, s) ∈ 𝒱` and `ψ(t) ≥ φ(t, s)` for all `s ∈ I` and `t ∈ (0, χ(s))`. -/
theorem proposition_10 (O : OMinimalStructure) (a : ℝ) (V : Set (EuclideanSpace ℝ (Fin 2)))
    (hVdef : V ∈ O.O 2) (hVsub : V ⊆ {z | 0 ≤ z 0 ∧ a ≤ z 1})
    (hVnhd : ∀ s, a ≤ s → V ∈ 𝓝[{z : EuclideanSpace ℝ (Fin 2) | 0 ≤ z 0 ∧ a ≤ z 1}] !₂[0, s])
    (φ : ℝ → ℝ → ℝ) (hφdef : DefinableOn O V (fun z => φ (z 0) (z 1)))
    (hφnn : ∀ z ∈ V, 0 ≤ φ (z 0) (z 1))
    (hφcont : ∀ s, a ≤ s → ContinuousWithinAt (fun z : EuclideanSpace ℝ (Fin 2) => φ (z 0) (z 1))
      V !₂[0, s])
    (hφ0 : ∀ s, a ≤ s → φ 0 s = 0) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ χ ψ : ℝ → ℝ,
      (∀ s, a ≤ s → χ s ∈ Set.Ioo 0 ε0) ∧ ContinuousOn χ (Set.Ici a) ∧
      DefinableOn1 O (Set.Ici a) χ ∧
      ContinuousOn ψ (Set.Ico 0 ε0) ∧ DefinableOn1 O (Set.Ico 0 ε0) ψ ∧
      (∀ t ∈ Set.Ico 0 ε0, 0 ≤ ψ t) ∧ ContDiffOn ℝ 1 ψ (Set.Ioo 0 ε0) ∧ ψ 0 = 0 ∧
      ∀ s, a ≤ s → ∀ t ∈ Set.Ioo 0 (χ s), !₂[t, s] ∈ V ∧ φ t s ≤ ψ t := by sorry

end ClarkeStrat.KL

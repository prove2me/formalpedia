-- Prove2me | Theorems.Thm_AsyncSA_Contraction_lemma1
-- name    : AsyncSA.Contraction.lemma1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:56.778171+00:00
-- url     : https://prove2.me/theorems/c976d570-346e-40cd-b913-6470302c74da
-- title:
--   Lemma 1 — convergence of a scalar stochastic approximation recursion
-- statement:
--   Let $\mathcal F(t)$ be an increasing filtration and let $\alpha(t)$, $w(t)$, and $B(t)$ be scalar random variables, with $\alpha(t)$ and $B(t)$ measurable at time $t$ and $w(t)$ measurable at time $t+1$. Suppose $w(t)$ has conditional mean zero and conditional second moment at most $B(t)$. Almost surely, let $0\le\alpha(t)\le1$, $\sum_t\alpha(t)=\infty$, $\sum_t\alpha(t)^2\le C$ for one deterministic $C$, and let the path $B(t)$ be bounded. If $W$ satisfies
--
--   $$W(t+1)=(1-\alpha(t))W(t)+\alpha(t)w(t),$$
--
--   then $W(t)\to0$ almost surely. The initial scalar $W(0)$ may be any finite random value.
--
--   This lemma controls the scalar noise recursion used in both convergence and boundedness arguments.
--
--   **Formalization Note** Conditional moments are generalized measurable-set statements, and both step-size series are encoded by partial sums. The paper's notation says $w(t-1)$ is $\mathcal F(t)$-measurable; the equivalent nonnegative-index condition is that $w(t)$ is $\mathcal F(t+1)$-measurable.
-- source:
--   Tsitsiklis, Asynchronous Stochastic Approximation and Q-Learning, Machine Learning 16 (1994), p. 190, §3, Lemma 1

import Mathlib
import Definitions.Def_AsyncSA_Contraction_Model

namespace AsyncSA.Contraction

open MeasureTheory Filter Topology

/-- Lemma 1, p. 190. The recursion may start from any finite random value. -/
theorem lemma1 {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ m₀) (α w B W : ℕ → Ω → ℝ) (C : ℝ)
    (hαmeas : ∀ t, Measurable[𝓕 t] (α t))
    (hwmeas : ∀ t, Measurable[𝓕 (t + 1)] (w t))
    (hBmeas : ∀ t, Measurable[𝓕 t] (B t))
    (hmean : ∀ t, CondMeanZero m₀ (𝓕 t) P (w t))
    (hsq : ∀ t, CondSqLe m₀ (𝓕 t) P (w t) (B t))
    (hαmem : ∀ᵐ ω ∂P, ∀ t, α t ω ∈ Set.Icc (0 : ℝ) 1)
    (hdiv : ∀ᵐ ω ∂P,
      Tendsto (fun T => ∑ t ∈ Finset.range T, α t ω) atTop atTop)
    (hsum : ∀ᵐ ω ∂P,
      ∀ T, ∑ t ∈ Finset.range T, α t ω ^ 2 ≤ C)
    (hBbound : ∀ᵐ ω ∂P, ∃ K : ℝ, ∀ t, |B t ω| ≤ K)
    (hW : ∀ t ω, W (t + 1) ω =
      (1 - α t ω) * W t ω + α t ω * w t ω) :
    ∀ᵐ ω ∂P, Tendsto (fun t => W t ω) atTop (𝓝 0) := by sorry

end AsyncSA.Contraction

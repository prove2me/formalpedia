-- Prove2me | Theorems.Thm_AsyncSA_Monotone_lemma1
-- name    : AsyncSA.Monotone.lemma1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:45.009399+00:00
-- url     : https://prove2.me/theorems/58a6810a-15c4-4957-a574-44f8942ddb1c
-- title:
--   Lemma 1 — W(t+1) = (1 − α(t))W(t) + α(t)w(t) converges to 0 w.p.1 for martingale-difference noise with bounded conditional variance
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $\{\mathcal F(t)\}_{t\ge0}$ an increasing sequence of σ-fields. For each $t$ let $\alpha(t)$, $w(t-1)$ and $B(t)$ be $\mathcal F(t)$-measurable scalar random variables, and let $C$ be a deterministic constant. Suppose that, with probability 1,
--
--   1. $E[w(t)\mid\mathcal F(t)]=0$ for all $t$;
--   2. $E[w^2(t)\mid\mathcal F(t)]\le B(t)$ for all $t$;
--   3. $\alpha(t)\in[0,1]$ for all $t$;
--   4. $\sum_{t=0}^\infty\alpha(t)=\infty$;
--   5. $\sum_{t=0}^\infty\alpha^2(t)\le C$;
--
--   and that the sequence $\{B(t)\}$ is bounded with probability 1. Let $W(t)$ satisfy
--   $$
--   W(t+1)=(1-\alpha(t))W(t)+\alpha(t)w(t),\qquad t\ge0,
--   $$
--   with $W(0)$ arbitrary. Then
--   $$
--   \lim_{t\to\infty}W(t)=0\quad\text{with probability 1.}
--   $$
--
--   This is the scalar stochastic approximation result on which the convergence analysis of the asynchronous algorithm rests: in §5 it is applied, component by component, to the accumulated noise $W_i(t)$.
--
--   **Formalization Note** The conditional expectations are generalized: (1) means $\int_S w(t)\,dP=0$ for every $S\in\mathcal F(t)$ on which $w(t)$ is integrable, and (2) means $\int_S w(t)^2\,dP\le\int_S B(t)^+\,dP$ in $[0,\infty]$ for every $S\in\mathcal F(t)$; no integrability of $w(t)$ is assumed, as in the paper. (4) is divergence of the partial sums to $+\infty$ and (5) bounds every partial sum by $C$. "$w(t-1)$ is $\mathcal F(t)$-measurable" is written as "$w(t)$ is $\mathcal F(t+1)$-measurable". The boundedness of $\{B(t)\}$ is $\sup_t|B(t)|<\infty$ on almost every sample path, with a bound that may depend on the path. The recursion holds on every sample path, and $W(0)$ is an arbitrary (not necessarily measurable) function.
-- source:
--   Tsitsiklis, Asynchronous Stochastic Approximation and Q-Learning, Machine Learning 16 (1994), p. 190, §3, Lemma 1

import Mathlib
import Definitions.Def_AsyncSA_Monotone_Model

namespace AsyncSA.Monotone

open MeasureTheory Filter Topology

theorem lemma1 {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ m0) (α w B W : ℕ → Ω → ℝ) (C : ℝ)
    (hα_meas : ∀ t, Measurable[𝓕 t] (α t))
    (hw_meas : ∀ t, Measurable[𝓕 (t + 1)] (w t))
    (hB_meas : ∀ t, Measurable[𝓕 t] (B t))
    (ha : ∀ t, CondMeanZero (𝓕 t) P (w t))
    (hb : ∀ t, CondSqLe (𝓕 t) P (w t) (B t))
    (hc : ∀ᵐ ω ∂P, ∀ t, α t ω ∈ Set.Icc (0 : ℝ) 1)
    (hd : ∀ᵐ ω ∂P, Tendsto (fun T => ∑ t ∈ Finset.range T, α t ω) atTop atTop)
    (he : ∀ᵐ ω ∂P, ∀ T, ∑ t ∈ Finset.range T, α t ω ^ 2 ≤ C)
    (hB_bdd : ∀ᵐ ω ∂P, ∃ K : ℝ, ∀ t, |B t ω| ≤ K)
    (hW : ∀ t ω, W (t + 1) ω = (1 - α t ω) * W t ω + α t ω * w t ω) :
    ∀ᵐ ω ∂P, Tendsto (fun t => W t ω) atTop (𝓝 0) := by sorry

end AsyncSA.Monotone

-- Prove2me | Theorems.Thm_FirstPriceLearning_ContextLowerBound_lemma_13
-- name    : FirstPriceLearning.ContextLowerBound.lemma_13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:32:18.078302+00:00
-- url     : https://prove2.me/theorems/12fb6107-ec36-485b-bf22-96b939481969
-- title:
--   Lemma 13: multiple-hypothesis testing lower bound [GHRZ19, Lemma 3]
-- statement:
--   Let $Q_1,\dots,Q_n$ be probability measures on a measurable space $(\Omega,\mathcal F)$ and let $\Psi:\Omega\to[n]$ be a measurable function (a test). Then
--   $$\frac1n\sum_{i=1}^n Q_i(\Psi\neq i)\ \ge\ \frac1{2n}\sum_{i=2}^n\exp\big(-D_{\mathrm{KL}}(Q_1\|Q_i)\big).$$
--
--   This lower-bounds the average error of any test among $n$ hypotheses in terms of KL divergences to a reference hypothesis; it is step (c) of the proof of Theorem 6.
--
--   **Formalization Note.** Paper index $i\in[n]$ is Lean index $i-1$, with $n=$ Lean $n+1\ge1$. KL divergence takes values in $[0,\infty]$, and $\exp(-\infty)$ is read as $0$: the term of an $i$ with infinite divergence is $0$, so no finiteness assumption is needed.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 36, Lemma 13 (quoting Gao, Han, Ren, Zhou, Batched Multi-armed Bandits Problem, NeurIPS 2019 [GHRZ19], Lemma 3, special case)

import Mathlib

open MeasureTheory InformationTheory

namespace FirstPriceLearning.ContextLowerBound

theorem lemma_13 {Ω : Type} [MeasurableSpace Ω] (n : ℕ) (Q : Fin (n + 1) → Measure Ω)
    (hQ : ∀ i, IsProbabilityMeasure (Q i)) (Ψ : Ω → Fin (n + 1)) (hΨ : Measurable Ψ) :
    1 / (2 * ((n : ℝ) + 1)) * ∑ i : Fin n,
        (if klDiv (Q 0) (Q i.succ) = ⊤ then 0
         else Real.exp (-(klDiv (Q 0) (Q i.succ)).toReal)) ≤
      1 / ((n : ℝ) + 1) * ∑ i : Fin (n + 1), (Q i {ω | Ψ ω ≠ i}).toReal := by sorry

end FirstPriceLearning.ContextLowerBound

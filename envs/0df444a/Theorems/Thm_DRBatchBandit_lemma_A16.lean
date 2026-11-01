-- Prove2me | Theorems.Thm_DRBatchBandit_lemma_A16
-- name    : DRBatchBandit.lemma_A16
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:23:58.919534+00:00
-- url     : https://prove2.me/theorems/6e7483a0-00c1-46f2-9c99-a3134758451a
-- title:
--   Lemma A16, p.51 — a density floor $\underline b$ gives $\sup_t|q_{\mathbf P_1}(t)-q_{\mathbf P_2}(t)|\le\frac1{\underline b}\sup_{x\in[0,M]}|F_{\mathbf P_1}(x)-F_{\mathbf P_2}(x)|$
-- statement:
--   Let $\mathbf P_1,\mathbf P_2$ be probability measures on $\mathbb R$ supported on $[0,M]$, and suppose $\mathbf P_1$ has a density $f_{\mathbf P_1}$ with $f_{\mathbf P_1}\ge\underline b>0$ on $[0,M]$. Then
--   $$\sup_{t\in[0,1]}|q_{\mathbf P_1}(t)-q_{\mathbf P_2}(t)|\le\frac1{\underline b}\sup_{x\in[0,M]}|F_{\mathbf P_1}(x)-F_{\mathbf P_2}(x)|,$$
--   where $F$ denotes a CDF and $q$ a quantile.
--
--   Together with Lemma 5 it bounds the estimation error of the robust value by a Kolmogorov distance of weighted empirical CDFs, in the continuous case of Theorem 2.
--
--   **Formalization Note** "Density $\ge\underline b$ on $[0,M]$" is encoded as $\mathbf P_1\ll\lambda$ and $\underline b\,\lambda(s)\le\mathbf P_1(s)$ for measurable $s\subseteq[0,M]$. The conclusion is stated for every real $T$ bounding $|F_{\mathbf P_1}-F_{\mathbf P_2}|$ on $[0,M]$, and for every $t\in(0,1]$.
--
--   Differences from the source:
--   - reading: sup over t ∈ [0, 1] → every t ∈ (0, 1]; reason: q_P(0) = −∞ for every P, so the printed supremum is undefined at t = 0
--   - encoding: positive density f_{P₁} ≥ b on [0, M] → P₁ ≪ Lebesgue and b·λ(s) ≤ P₁(s) for measurable s ⊆ [0, M]; reason: equivalent by the Radon–Nikodym theorem
--   - encoding: sup_t |q₁ − q₂| ≤ (1/b) sup_x |F₁ − F₂| → |q₁(t) − q₂(t)| ≤ T/b for every T bounding |F₁ − F₂| on [0, M]; reason: equivalent formulation without a real supremum
-- source:
--   Si, Zhang, Zhou & Blanchet, Distributionally Robust Batch Contextual Bandits, arXiv:2006.05630v7, Lemma A16, p.51. PDF sha256 ac485985feb75d33b603f06f5a5d93c52077877db7be11de3d71107c7c374b02

import Mathlib
import Definitions.Def_DRBatchBandit_ScalarDual

open MeasureTheory ProbabilityTheory

namespace DRBatchBandit

/-- Lemma A16 (Si, Zhang, Zhou & Blanchet, arXiv:2006.05630v7, p.51): if probability measures
`P₁, P₂` are supported on `[0, M]` and `P₁` has a density `f_{P₁} ≥ b > 0` on `[0, M]`, then
`sup_{t ∈ [0,1]} |q_{P₁}(t) − q_{P₂}(t)| ≤ (1/b) sup_{x ∈ [0,M]} |F_{P₁}(x) − F_{P₂}(x)|`.

**Formalization Note.** The density condition is `P₁ ≪ λ` with `b · λ(s) ≤ P₁(s)` for measurable
`s ⊆ [0, M]`. The conclusion is stated for every real `T` bounding `|F_{P₁} − F_{P₂}|` on
`[0, M]`, and for `t ∈ (0, 1]` (at `t = 0` both quantiles are `−∞` in the paper). -/
theorem lemma_A16 (P₁ P₂ : Measure ℝ) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (Mrew b : ℝ) (hb : 0 < b) (h₁ : P₁ (Set.Icc 0 Mrew) = 1) (h₂ : P₂ (Set.Icc 0 Mrew) = 1)
    (hac : P₁ ≪ volume)
    (hdens : ∀ s ⊆ Set.Icc 0 Mrew, MeasurableSet s → ENNReal.ofReal b * volume s ≤ P₁ s)
    (T : ℝ) (hT : ∀ x ∈ Set.Icc 0 Mrew, |cdf P₁ x - cdf P₂ x| ≤ T) :
    ∀ t ∈ Set.Ioc (0 : ℝ) 1, |quantile P₁ t - quantile P₂ t| ≤ T / b := by sorry

end DRBatchBandit

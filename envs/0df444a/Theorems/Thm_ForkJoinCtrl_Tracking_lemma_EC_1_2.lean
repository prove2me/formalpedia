-- Prove2me | Theorems.Thm_ForkJoinCtrl_Tracking_lemma_EC_1_2
-- name    : ForkJoinCtrl.Tracking.lemma_EC_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:24.347402+00:00
-- url     : https://prove2.me/theorems/2664d996-0e38-423e-95a6-efebe6147488
-- title:
--   Lemma EC.1.2, p. EC1 — Chernoff bound: P(max_{N≤⌊ar⌋} |Σ_{n≤N}(X_n − x)| > br) ≤ 2e^{−C34 r} for large r
-- statement:
--   Let $X_1,X_2,\dots$ be nonnegative i.i.d. random variables with $\mathbf E[X_1]=x>0$, and suppose there is $\bar\alpha>0$ with $\mathbf E[e^{\alpha X_1}]<\infty$ for all $\alpha\in(-\bar\alpha,\bar\alpha)$. Let $a,b>0$. Then there are $C_{34}>0$ and $r_{14}\in\mathbb N_+$ such that for all $r\ge r_{14}$
--
--   $$\mathbf P\Big(\max_{N\in\{1,\dots,\lfloor ar\rfloor\}}\Big|\sum_{n=1}^{N}(X_n-x)\Big|>br\Big)\le 2e^{-C_{34}r}.$$
--
--   This exponential bound, applied to inter-arrival and service times, drives the tail estimates of Lemmas 5–8.
--
--   **Formalization Note** The maximum exceeds $br$ exactly when some $N\in\{1,\dots,\lfloor ar\rfloor\}$ does; for $\lfloor ar\rfloor=0$ the event is empty. Independence is mutual independence of $(X_n)_{n\ge1}$; nonnegativity is almost sure. $C_{34}$ and $r_{14}$ may depend on $a$, $b$ and the law of $X_1$, not on $r$.
-- source:
--   Özkan, Control of Fork-Join Processing Networks with Multiple Job Types and Parallel Shared Resources, arXiv:2002.01496v1, p. EC1, §EC.1, Lemma EC.1.2

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ForkJoinCtrl.Tracking

theorem lemma_EC_1_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (x : ℝ)
    (hmeas : ∀ n, Measurable (X n))
    (hnonneg : ∀ n, 1 ≤ n → ∀ᵐ ω ∂P, 0 ≤ X n ω)
    (hindep : iIndepFun (fun n : {n : ℕ // 1 ≤ n} => X n.1) P)
    (hident : ∀ n, 1 ≤ n → IdentDistrib (X n) (X 1) P P)
    (hint : Integrable (X 1) P) (hmean : ∫ ω, X 1 ω ∂P = x) (hx : 0 < x)
    (hmom : ∃ αbar : ℝ, 0 < αbar ∧ ∀ α ∈ Set.Ioo (-αbar) αbar,
      Integrable (fun ω => Real.exp (α * X 1 ω)) P)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ C34 : ℝ, 0 < C34 ∧ ∃ r14 : ℕ, 1 ≤ r14 ∧ ∀ r : ℕ, r14 ≤ r →
      P {ω | ∃ Nn ∈ Finset.Icc 1 ⌊a * r⌋₊, b * r < |∑ n ∈ Finset.Icc 1 Nn, (X n ω - x)|} ≤
        ENNReal.ofReal (2 * Real.exp (-C34 * r)) := by sorry

end ForkJoinCtrl.Tracking

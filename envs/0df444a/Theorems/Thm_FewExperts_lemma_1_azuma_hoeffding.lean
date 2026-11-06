-- Prove2me | Theorems.Thm_FewExperts_lemma_1_azuma_hoeffding
-- name    : FewExperts.lemma_1_azuma_hoeffding
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:52:16.603243+00:00
-- url     : https://prove2.me/theorems/f3889ae7-1c49-446d-8f0e-95c8ea58dead
-- title:
--   Lemma 1 — Azuma–Hoeffding: $\Pr[\sum X_t\ge\sum\mu_t+\lambda]\le e^{-2\lambda^2/\sum(b_t-a_t)^2}$, both tails
-- statement:
--   Let $X_1,\dots,X_n$ be random variables on a probability space, adapted to a filtration $(\mathcal F_t)$. Let $a_t,b_t,\mu_t$ be constants with $a_t\le X_t\le b_t$ almost surely.
--
--   1. If $\mathbb E[X_t\mid\mathcal F_{t-1}]\le\mu_t$ almost surely for every $t$, then for every $\lambda>0$
--   $$
--   \Pr\Bigl[\sum_{t=1}^n X_t\ge\sum_{t=1}^n\mu_t+\lambda\Bigr]\le\exp\Bigl(-\frac{2\lambda^2}{\sum_{t=1}^n(b_t-a_t)^2}\Bigr).
--   $$
--   2. If $\mathbb E[X_t\mid\mathcal F_{t-1}]\ge\mu_t$ almost surely for every $t$, then for every $\lambda>0$
--   $$
--   \Pr\Bigl[\sum_{t=1}^n X_t\le\sum_{t=1}^n\mu_t-\lambda\Bigr]\le\exp\Bigl(-\frac{2\lambda^2}{\sum_{t=1}^n(b_t-a_t)^2}\Bigr).
--   $$
--
--   The paper uses this inequality for the failure indicators of the epochs and for the gap between sampled and mixed gains.
--
--   Differences from the source:
--   - generalization: conditioning on X₁, …, X_{t−1} → conditioning on ℱ_{t−1} for any filtration ℱ to which X is adapted; reason: the natural filtration of X is such a filtration, so the statement specializes to the paper's
--   - encoding: Pr[bad event] ≤ β → the (outer) measure of the bad event is ≤ ENNReal.ofReal β; reason: equal for measurable events; no measurability statement is needed
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), Lemma 1, pp.13–14 (PDF pp.14–15), citing Cesa-Bianchi–Lugosi 2006, Lemma A.7

import Mathlib

namespace FewExperts

open MeasureTheory ProbabilityTheory

/-- **Lemma 1 (Azuma–Hoeffding [CBL06, Lemma A.7]), both tails.**
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), Lemma 1, p.13 (PDF 14–15): "Let X₁, …, X_n be random variables such that
a_t ≤ X_t ≤ b_t almost surely and E[X_t | X₁, …, X_{t−1}] ≤ μ_t for every t. Then, for every
λ > 0, Pr[∑_{t=1}^n X_t ≥ ∑_{t=1}^n μ_t + λ] ≤ exp(−2λ²/∑_{t=1}^n (b_t − a_t)²). The analogous
lower-tail bound holds when the inequality on the conditional expectation is reversed."

The variables are `X 1, …, X n` on a probability space `(Ω, P)`; the constants are `a t`, `b t`,
`μ t`; the conditioning is on `ℱ (t − 1)` for a filtration `ℱ` to which `X` is adapted.

**Formalization Note** The paper conditions on `X₁, …, X_{t−1}`; here it is any filtration to
which `X` is adapted (the natural filtration is one). Probabilities are stated as upper bounds on
the (outer) measure of the event. `λ` is written `lam`. -/
theorem lemma_1_azuma_hoeffding {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (hX : StronglyAdapted ℱ X)
    (n : ℕ) (a b μ : ℕ → ℝ)
    (hab : ∀ t ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, a t ≤ X t ω ∧ X t ω ≤ b t) :
    ((∀ t ∈ Finset.Icc 1 n, P[X t | ℱ (t - 1)] ≤ᵐ[P] fun _ => μ t) →
      ∀ lam : ℝ, 0 < lam →
        P {ω | ∑ t ∈ Finset.Icc 1 n, μ t + lam ≤ ∑ t ∈ Finset.Icc 1 n, X t ω} ≤
          ENNReal.ofReal (Real.exp (-2 * lam ^ 2 / ∑ t ∈ Finset.Icc 1 n, (b t - a t) ^ 2))) ∧
    ((∀ t ∈ Finset.Icc 1 n, (fun _ => μ t) ≤ᵐ[P] P[X t | ℱ (t - 1)]) →
      ∀ lam : ℝ, 0 < lam →
        P {ω | ∑ t ∈ Finset.Icc 1 n, X t ω ≤ ∑ t ∈ Finset.Icc 1 n, μ t - lam} ≤
          ENNReal.ofReal (Real.exp (-2 * lam ^ 2 / ∑ t ∈ Finset.Icc 1 n, (b t - a t) ^ 2))) := by sorry

end FewExperts

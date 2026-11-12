-- Prove2me | Theorems.Thm_ConvexRMDP_lemma_4_1
-- name    : ConvexRMDP.lemma_4_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-03T05:16:12.436006+00:00
-- url     : https://prove2.me/theorems/7e994e4e-aa24-4a57-93d9-1015186c0e94
-- title:
--   Lemma 4.1 (Donsker–Varadhan): $\max_{q} q^\top y - \frac1b\mathrm{KL}(q,q_0) = \frac1b\log\sum_a q_{0,a}e^{b y_a}$
-- statement:
--   Let $\mathcal A$ be a finite set, $q_0 \in \Delta(\mathcal A)$, $y \in \mathbb R^{\mathcal A}$ and $b > 0$. Then
--   $$
--   \max_{q \in \Delta(\mathcal A)} q^\top y - \frac1b \mathrm{KL}(q, q_0) = \frac1b \log\left(\sum_{a \in \mathcal A} q_{0,a} \exp(b \cdot y_a)\right),
--   $$
--   and the maximum is attained. The reference distribution $q_0$ may have zero entries.
--
--   This is the Donsker–Varadhan variational formula: the convex conjugate of the negative entropy is the log-sum-exp function. Applied to $\tilde T$ it gives the closed form (4.3).
--
--   **Formalization Note** Since $\mathrm{KL}(q, q_0) = +\infty$ unless $q \ll q_0$, such $q$ have objective $-\infty$; the maximum is taken over the $q \in \Delta(\mathcal A)$ with $q \ll q_0$, where the divergence is the finite sum.
--
--   Differences from the source:
--   - encoding: KL(q,q₀) = +∞ unless q ≪ q₀; max over all q ∈ Δ(A) → max over q ∈ Δ(A) with AbsCont q q₀, with the finite kl; reason: q with KL = +∞ have objective −∞ and never attain the maximum; same value.
--   - reading: regularization scalar b in (4.1) → b > 0; reason: the paper's setting of §4.2 ("For b > 0"); with b ≤ 0 the term −(1/b)KL is not a regularizer.
--   - encoding: max … = value → IsGreatest of the set of objective values; reason: states that the value is attained and is the maximum.
-- source:
--   Grand-Clément & Petrik, On the Convex Formulations of Robust Markov Decision Processes, arXiv:2209.10187v2 (13 Dec 2023), Lemma 4.1, (4.2), p.11

import Mathlib
import Definitions.Def_ConvexRMDP_kl

namespace ConvexRMDP

/-- **Lemma 4.1 (Donsker–Varadhan)** (Grand-Clément & Petrik, arXiv:2209.10187v2, (4.2), p.11): for
`q₀ ∈ Δ(A)` and `y ∈ ℝ^A`,
`max_{q ∈ Δ(A)} qᵀy − (1/b) KL(q, q₀) = (1/b) log(∑_a q₀_a exp(b · y_a))`.

**Formalization Note.** `KL(q, q₀) = +∞` unless `q ≪ q₀` (p.10), so such `q` never attain the
maximum; the maximum is taken over the `q ∈ Δ(A)` with `AbsCont q q₀`, where `kl` is the paper's
finite value. `q₀` may have zero entries. `b > 0` is the regularization scalar. `IsGreatest` states
both that the value is attained and that it is the maximum. -/
theorem lemma_4_1 {A : Type*} [Fintype A] (b : ℝ) (hb : 0 < b) (q₀ : A → ℝ)
    (hq₀ : q₀ ∈ stdSimplex ℝ A) (y : A → ℝ) :
    IsGreatest {t | ∃ q ∈ stdSimplex ℝ A, AbsCont q q₀ ∧ t = ∑ a, q a * y a - kl q q₀ / b}
      (Real.log (∑ a, q₀ a * Real.exp (b * y a)) / b) := by sorry

end ConvexRMDP

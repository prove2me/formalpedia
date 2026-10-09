-- Prove2me | Theorems.Thm_FastCLO_ERM_lemma_2
-- name    : FastCLO.ERM.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:17:25.397008+00:00
-- url     : https://prove2.me/theorems/ec7f3933-c3c5-41ba-b720-2b4267caba5c
-- title:
--   Lemma 2 (Bousquet's inequality) — concentration of the supremum of a countable bounded empirical process
-- statement:
--   Let $Q$ be a probability measure on a measurable space $\mathcal X$, and let $\mathcal H = \{h_i : i \in I\}$ be a nonempty countable family of measurable real functions on $\mathcal X$ with
--
--   $$\sup_i \mathbb E_Q(h_i^2) \le \delta^2, \qquad \sup_i \|h_i\|_\infty \le \bar H$$
--
--   for constants $\delta$ and $\bar H > 0$. Let $X_1, \dots, X_n$ ($n \ge 1$) be i.i.d. with law $Q$, write $\mathbb E_n(h) = \frac1n\sum_{j=1}^n h(X_j)$, and let $S = \sup_i(\mathbb E_n(h_i) - \mathbb E_Q(h_i))$. Then for every $t > 0$,
--
--   $$\mathbb P\left(S - \mathbb E(S) \ge \sqrt{\frac{2(\delta^2 + 4\bar H\,\mathbb E(S))\,t}{n}} + \frac{2\bar H t}{3n}\right) \le \exp(-t).$$
--
--   This is Bousquet's version of Talagrand's concentration inequality for suprema of empirical processes; the paper applies it to a normalized excess-loss class of policies.
--
--   **Formalization Note** $\|h\|_\infty$ is the essential supremum, so the bound $|h_i| \le \bar H$ is required $Q$-almost everywhere. The family is nonempty, since an empty supremum is $0$ in Lean rather than $-\infty$. The hypothesis $\bar H > 0$ is added: at $\bar H = \delta = 0$ every $h_i$ vanishes almost everywhere, the threshold is $0$, and the event has probability $1$.
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, Lemma 2, A.4.2, p. 23 (Bousquet 2002)

import Mathlib
open MeasureTheory ProbabilityTheory

namespace FastCLO.ERM

/-- **Lemma 2** (Bousquet's inequality, as quoted by Hu, Kallus, Mao, *Fast Rates for Contextual
Linear Optimization*, arXiv:2011.03030v3, A.4.2, p. 23). Let `H = {h_i}` be a countable family of
measurable functions with `sup_i E_Q(h_i²) ≤ δ²` and `sup_i ‖h_i‖_∞ ≤ H̄`. Let
`S = sup_i (E_n(h_i) − E_Q(h_i))` on `n` i.i.d. draws from `Q`. Then for every `t > 0`,
`P(S − E(S) ≥ √(2(δ² + 4H̄E(S))t/n) + 2H̄t/(3n)) ≤ exp(−t)`.

Formalization Note: the sample space is an arbitrary measurable space; the family is indexed by a
nonempty countable type (an empty supremum would be `0` in Lean, not `−∞`). `‖h‖_∞` is read as
the essential supremum (`|h_i| ≤ H̄` `Q`-a.e.). `0 < H̄` is added: at `H̄ = δ = 0` every `h_i`
vanishes a.e., the threshold is `0`, and the event has probability `1`, so the printed statement
needs it (Bousquet's inequality is stated for functions normalized by a positive sup-norm bound).
`1 ≤ n` because the page divides by `n`. -/
theorem lemma_2 {𝒳 : Type*} [MeasurableSpace 𝒳] (Q : Measure 𝒳) [IsProbabilityMeasure Q]
    {ι : Type*} [Countable ι] [Nonempty ι] (h : ι → 𝒳 → ℝ) (hmeas : ∀ i, Measurable (h i))
    (δ Hbar : ℝ) (hHbar : 0 < Hbar) (h2 : ∀ i, ∫ x, h i x ^ 2 ∂Q ≤ δ ^ 2)
    (hinf : ∀ i, ∀ᵐ x ∂Q, |h i x| ≤ Hbar) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 < t) :
    let S : (Fin n → 𝒳) → ℝ := fun D =>
      ⨆ i, ((1 / (n : ℝ)) * ∑ j, h i (D j) - ∫ x, h i x ∂Q)
    let ES : ℝ := ∫ D, S D ∂(Measure.pi fun _ : Fin n => Q)
    Measure.pi (fun _ : Fin n => Q)
        {D | Real.sqrt (2 * (δ ^ 2 + 4 * Hbar * ES) * t / n) + 2 * Hbar * t / (3 * n) ≤ S D - ES}
      ≤ ENNReal.ofReal (Real.exp (-t)) := by sorry

end FastCLO.ERM

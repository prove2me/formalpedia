-- Prove2me | Theorems.Thm_BestBothWorlds_SAO_bernstein_martingale_variance
-- name    : BestBothWorlds.SAO.bernstein_martingale_variance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:58:34.198492+00:00
-- url     : https://prove2.me/theorems/c986c950-5f25-4f69-874f-000a41243356
-- title:
--   Lemma 4.4 — Bernstein's inequality for martingales with the random variance $V_n$
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space with a filtration $(\mathcal F_t)_{t\ge0}$, let $n\ge1$, and let $X_1,\dots,X_n$ be real random variables such that each $X_t$ is $\mathcal F_t$-measurable, $\mathbb E(X_t\mid\mathcal F_{t-1})=0$, and $|X_t|\le b$ for a constant $b>0$. Let $V_n=\sum_{t=1}^n\mathbb E(X_t^2\mid\mathcal F_{t-1})$ be the (random) predictable quadratic variation. Then for every $\delta>0$, with probability at least $1-\delta$,
--   $$\sum_{t=1}^n X_t\le\sqrt{4V_n\log(n\delta^{-1})+5b^2\log^2(n\delta^{-1})}.$$
--
--   Unlike Freedman's inequality (Theorem 4.3), the right-hand side involves the random variance $V_n$ and no fixed variance level. This is the form used to prove Lemmas 4.5 and 4.7.
--
--   **Formalization Note** The bound $|X_t|\le b$ is required only almost surely. Integrability of $X_t$ and $X_t^2$ follows from measurability and boundedness, so it is not assumed separately.
-- source:
--   Bubeck & Slivkins, The best of both worlds: stochastic and adversarial bandits, arXiv:1202.4473v1, p. 14, Lemma 4.4

import Mathlib

open MeasureTheory

namespace BestBothWorlds.SAO

/-- Lemma 4.4 (Bubeck–Slivkins, p. 14): Bernstein's inequality for martingales with the random
predictable variation `V_n = ∑_{t=1}^n E(X_t² | F_{t-1})`. -/
theorem bernstein_martingale_variance {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (b : ℝ) (hb : 0 < b)
    (hmeas : ∀ t ∈ Finset.Icc 1 n, Measurable[ℱ t] (X t))
    (hmds : ∀ t ∈ Finset.Icc 1 n, P[X t | ℱ (t - 1)] =ᵐ[P] 0)
    (hbd : ∀ t ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, |X t ω| ≤ b)
    (δ : ℝ) (hδ : 0 < δ) :
    1 - δ ≤ P.real {ω | ∑ t ∈ Finset.Icc 1 n, X t ω ≤
      Real.sqrt (4 * (∑ t ∈ Finset.Icc 1 n, P[fun ω' => X t ω' ^ 2 | ℱ (t - 1)] ω) *
          Real.log (n / δ) + 5 * b ^ 2 * Real.log (n / δ) ^ 2)} := by sorry

end BestBothWorlds.SAO

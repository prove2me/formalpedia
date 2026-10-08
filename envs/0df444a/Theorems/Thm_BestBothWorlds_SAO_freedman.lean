-- Prove2me | Theorems.Thm_BestBothWorlds_SAO_freedman
-- name    : BestBothWorlds.SAO.freedman
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:58:25.790211+00:00
-- url     : https://prove2.me/theorems/fd6fc9ec-afb0-44bb-b6b4-5873f348ee03
-- title:
--   Theorem 4.3 — Bernstein's inequality for martingales (Freedman)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space with filtration $(\mathcal F_t)_{t\ge0}$, and let $n\ge1$. For $1\le t\le n$, suppose $X_t$ is $\mathcal F_t$-measurable, has conditional mean zero given $\mathcal F_{t-1}$, and satisfies $|X_t|\le b$ almost surely, where $b>0$. Write $V_n=\sum_{t=1}^n\mathbb E[X_t^2\mid\mathcal F_{t-1}]$. For every $\varepsilon>0$ and variance level $V\in\mathbb R$,
--   $$P\left(\sum_{t=1}^n X_t\ge\varepsilon,\ V_n\le V\right)\le\exp\left(-\frac{\varepsilon^2}{2V+2b\varepsilon/3}\right).$$
--
--   **Formalization Note** The almost-sure bound suffices for the probability inequality and implies integrability. The page does not explicitly restrict $V$; the Lean statement quantifies over every real $V$.
-- source:
--   Bubeck & Slivkins, The best of both worlds: stochastic and adversarial bandits, arXiv:1202.4473v1, p. 14, Theorem 4.3, eq. (19)

import Mathlib

open MeasureTheory

namespace BestBothWorlds.SAO

/-- Theorem 4.3, equation (19) (p. 14): Freedman's Bernstein inequality with the paper's
two-sided bound `|X_t| ≤ b` and predictable variation `V_n`. -/
theorem freedman {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ) (X : ℕ → Ω → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (b : ℝ) (hb : 0 < b)
    (hmeas : ∀ t ∈ Finset.Icc 1 n, Measurable[ℱ t] (X t))
    (hmds : ∀ t ∈ Finset.Icc 1 n, P[X t | ℱ (t - 1)] =ᵐ[P] 0)
    (hbd : ∀ t ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, |X t ω| ≤ b)
    (ε V : ℝ) (hε : 0 < ε) :
    P.real {ω | ε ≤ ∑ t ∈ Finset.Icc 1 n, X t ω ∧
        ∑ t ∈ Finset.Icc 1 n, P[fun ω' => X t ω' ^ 2 | ℱ (t - 1)] ω ≤ V} ≤
      Real.exp (-ε ^ 2 / (2 * V + 2 * b * ε / 3)) := by sorry

end BestBothWorlds.SAO

-- Prove2me | Theorems.Thm_DecDepSO_lemma_A_1
-- name    : DecDepSO.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:15:45.567608+00:00
-- url     : https://prove2.me/theorems/12bcdbc4-664b-4ff2-96c6-7d546e7d8ab9
-- title:
--   Lemma A.1 — the partial products $\Gamma_t=\prod_{i=1}^t(1-\delta_i)$ satisfy $\sum_{i=1}^t\frac{\delta_i}{\Gamma_i}+1=\frac1{\Gamma_t}$
-- statement:
--   Let $(\delta_t)_{t\ge0}$ be a sequence of weights in $(0,1)$ and let $\Gamma_t:=\prod_{i=1}^t(1-\delta_i)$ (so $\Gamma_0=1$). Then for every $t\ge0$,
--   $$
--   \sum_{i=1}^t\frac{\delta_i}{\Gamma_i}+1=\frac1{\Gamma_t}.
--   $$
--
--   The identity says that $\Gamma_t$ and the numbers $\Gamma_t\delta_i/\Gamma_i$, $1\le i\le t$, are nonnegative weights summing to one; these are the coefficients that express the running average $\hat x_t$ as a convex combination of $x_0,\dots,x_t$ in Lemma A.2 and Corollary A.3.
--
--   **Formalization Note** $t=0$ is included (empty sum, $\Gamma_0=1$).
--
--   Differences from the source: none.
-- source:
--   Drusvyatskiy, Xiao, Stochastic optimization with decision-dependent distributions, arXiv:2011.11173v2, Lemma A.1, p.47

import Mathlib

namespace DecDepSO

/-- **Lemma A.1 (partial products).**
Drusvyatskiy, Xiao, *Stochastic optimization with decision-dependent distributions*,
arXiv:2011.11173v2, Lemma A.1, p.47: "Consider a sequence of weights {δt}t≥0 in (0, 1). Then the
partial products Γt = ∏_{i=1}^t (1 − δi) satisfy the equation ∑_{i=1}^t δi/Γi + 1 = 1/Γt."

For weights `δ_t ∈ (0, 1)`, `t ≥ 0`, and every `t ∈ ℕ`, with `Γ_t = ∏_{i=1}^t (1 − δ_i)`,
`∑_{i=1}^t δ_i/Γ_i + 1 = 1/Γ_t`.

**Formalization Note.** `t = 0` is included: the sum is empty and `Γ_0 = 1`. -/
theorem lemma_A_1 (δ : ℕ → ℝ) (hδ : ∀ t, 0 < δ t ∧ δ t < 1) (t : ℕ) :
    (∑ i ∈ Finset.Icc 1 t, δ i / ∏ j ∈ Finset.Icc 1 i, (1 - δ j)) + 1 =
      1 / ∏ i ∈ Finset.Icc 1 t, (1 - δ i) := by sorry

end DecDepSO

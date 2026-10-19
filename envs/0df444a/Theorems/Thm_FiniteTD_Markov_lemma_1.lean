-- Prove2me | Theorems.Thm_FiniteTD_Markov_lemma_1
-- name    : FiniteTD.Markov.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:22.258565+00:00
-- url     : https://prove2.me/theorems/25798e9d-7207-4b03-8100-66b993d9a510
-- title:
--   Lemma 1, p. 6 — norm equivalence: √ω‖θ‖₂ ≤ ‖V_θ‖_D ≤ ‖θ‖₂
-- statement:
--   Let $\pi$ be a probability vector on a finite set $S$, let $\phi(s)\in\mathbb{R}^d$ ($d\ge1$) be feature vectors with $\|\phi(s)\|_2\le1$, and let $\omega>0$ be the minimum eigenvalue of $\Sigma=\sum_s\pi(s)\phi(s)\phi(s)^\top$. Then for every $\theta\in\mathbb{R}^d$,
--   $$\sqrt{\omega}\,\|\theta\|_2 \;\le\; \|V_\theta\|_D \;\le\; \|\theta\|_2,$$
--   where $\|V_\theta\|_D = \big(\sum_s\pi(s)(\phi(s)^\top\theta)^2\big)^{1/2}$.
--
--   The lemma converts between the steady-state value-function norm and the parameter norm; it is how bounds on $\|V_{\theta^*}-V_\theta\|_D$ become bounds on $\|\theta^*-\theta\|_2$ in parts (b) and (c) of Theorem 3.
-- source:
--   Bhandari, Russo & Singal, A Finite Time Analysis of Temporal Difference Learning With Linear Function Approximation, arXiv:1806.02450v2, p. 6, Lemma 1

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting

namespace FiniteTD.Markov

theorem lemma_1 {S : Type} [Fintype S] {d : ℕ} [NeZero d]
    (π : S → ℝ) (φ : S → EuclideanSpace ℝ (Fin d)) (ω : ℝ)
    (hπ0 : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1) (hφ : ∀ s, ‖φ s‖ ≤ 1)
    (hω : IsMinEig π φ ω) (hω0 : 0 < ω) :
    ∀ θ : EuclideanSpace ℝ (Fin d),
      Real.sqrt ω * ‖θ‖ ≤ Real.sqrt (dNormSq π φ θ) ∧ Real.sqrt (dNormSq π φ θ) ≤ ‖θ‖ := by sorry

end FiniteTD.Markov

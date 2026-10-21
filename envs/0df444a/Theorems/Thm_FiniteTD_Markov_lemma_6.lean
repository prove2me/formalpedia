-- Prove2me | Theorems.Thm_FiniteTD_Markov_lemma_6
-- name    : FiniteTD.Markov.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:13.956675+00:00
-- url     : https://prove2.me/theorems/b9c0b311-ddc3-40c7-aeca-0d386f996aa5
-- title:
--   Lemma 6, p. 17 — gradient bound: ‖g_t(θ)‖₂ ≤ rmax + 2‖θ‖₂
-- statement:
--   Let rewards satisfy $|R(s,s')|\le r_{\max}$, features satisfy $\|\phi(s)\|_2\le1$, and $0\le\gamma<1$. Then for every $\theta\in\mathbb{R}^d$ and every transition $(s,s')$,
--   $$\big\|\big(R(s,s')+\gamma\phi(s')^\top\theta-\phi(s)^\top\theta\big)\phi(s)\big\|_2\;\le\;r_{\max}+2\|\theta\|_2 .$$
--   In the paper's notation, $\|g_t(\theta)\|_2\le r_{\max}+2\|\theta\|_2$ with probability 1.
--
--   On the ball $\|\theta\|_2\le R$ kept by projected TD this gives the uniform bound $G=r_{\max}+2R$ used throughout the analysis.
--
--   **Formalization Note** "With probability 1" is stated as "for every transition", which is the same statement on a finite state space.
-- source:
--   Bhandari, Russo & Singal, A Finite Time Analysis of Temporal Difference Learning With Linear Function Approximation, arXiv:1806.02450v2, p. 17, Lemma 6

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting

namespace FiniteTD.Markov

theorem lemma_6 {S : Type} [Fintype S] {d : ℕ}
    (Rw : S → S → ℝ) (rmax γ : ℝ) (φ : S → EuclideanSpace ℝ (Fin d))
    (hRw : ∀ s s', |Rw s s'| ≤ rmax) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hφ : ∀ s, ‖φ s‖ ≤ 1) :
    ∀ (θ : EuclideanSpace ℝ (Fin d)) (s s' : S),
      ‖tdDir γ Rw φ θ s s'‖ ≤ rmax + 2 * ‖θ‖ := by sorry

end FiniteTD.Markov

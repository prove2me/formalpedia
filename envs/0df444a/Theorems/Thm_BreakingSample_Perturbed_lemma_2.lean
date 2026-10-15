-- Prove2me | Theorems.Thm_BreakingSample_Perturbed_lemma_2
-- name    : BreakingSample.Perturbed.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:05:09.876439+00:00
-- url     : https://prove2.me/theorems/d1b0ea5d-d125-4dc3-9e5c-041f29329d03
-- title:
--   Lemma 2 — Bernstein condition gives uniform policy-value error
-- statement:
--   Fix a deterministic policy $\pi$ and two transition kernels $P$ and $\widehat P$ on a finite discounted MDP. Let $V^{(l)}$ be the auxiliary vectors of (36). If $\beta_1>0$ and, for every integer $0\le l\le\log(e/(1-\gamma))$, the componentwise Bernstein condition (37) holds, and $N>16e^2\beta_1/(1-\gamma)$, then
--
--   $$\|\widehat V^\pi-V^\pi\|_\infty\le\frac{6}{1-\gamma}\sqrt{\frac{\beta_1}{N(1-\gamma)}}.$$
--
--   This deterministic implication lets a later argument handle policies selected from the data.
--
--   **Formalization Note** The statement allows any stochastic $\widehat P$; empirical origin is unnecessary for this deterministic lemma.
-- source:
--   arXiv:2005.12900v8, Lemma 2, (36)–(38), p. 15

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel

namespace BreakingSample.Perturbed

open FoundationsML.ReinforcementLearning

/-- Lemma 2 and (37)–(38), arXiv:2005.12900v8, p. 15. -/
theorem lemma_2 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P Phat : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (π : S → A)
    (N : ℕ) (β₁ : ℝ) (hM : IsDiscountedMDP P r γ)
    (hPhat : IsTransitionKernel Phat) (hβ : 0 < β₁)
    (hBernstein : ∀ l : ℕ, (l : ℝ) ≤ Real.log (Real.exp 1 / (1 - γ)) →
      ∀ s, |∑ s', (Phat s (π s) s' - P s (π s) s') * auxV P r γ π l s'| ≤
        Real.sqrt (β₁ / N) * Real.sqrt (varPi P π (auxV P r γ π l) s) +
          β₁ * ‖auxV P r γ π l‖ / N)
    (hN : (16 * (Real.exp 1) ^ 2 / (1 - γ)) * β₁ < (N : ℝ)) :
    ‖(fun s => value Phat r γ π s - value P r γ π s)‖ ≤
      6 / (1 - γ) * Real.sqrt (β₁ / (N * (1 - γ))) := by sorry

end BreakingSample.Perturbed

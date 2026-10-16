-- Prove2me | Theorems.Thm_BreakingSample_Conservative_lemma_2
-- name    : BreakingSample.Conservative.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:01:45.927493+00:00
-- url     : https://prove2.me/theorems/3b3b5835-e4f6-4c59-8c19-ace48f9e245f
-- title:
--   Lemma 2, p. 15 — under the Bernstein-type condition (37) and N > 16e²β₁/(1−γ), ‖V̂^π − V^π‖∞ ≤ (6/(1−γ))√(β₁/(N(1−γ)))
-- statement:
--   Let $(\mathcal S,\mathcal A,P,r,\gamma)$ be a finite discounted MDP with rewards in $[0,1]$ and $\gamma\in(0,1)$, let $\widehat P$ be another transition kernel, $\pi$ a deterministic policy, and $V^{(l)}$ the auxiliary vectors (36) of $(P, r, \pi)$. Suppose there is $\beta_1 > 0$ such that, entrywise,
--
--   $$\big|(\widehat P_\pi - P_\pi)V^{(l)}\big| \le \sqrt{\frac{\beta_1}{N}}\sqrt{\mathrm{Var}_{P_\pi}\big[V^{(l)}\big]} + \frac{\beta_1\|V^{(l)}\|_\infty}{N}\mathbf 1 \qquad \text{for all integers } 0 \le l \le \log\Big(\frac{e}{1-\gamma}\Big),$$
--
--   and that $N > \frac{16e^2}{1-\gamma}\beta_1$. Then the value functions $V^\pi = (I-\gamma P_\pi)^{-1}r_\pi$ and $\widehat V^\pi = (I-\gamma\widehat P_\pi)^{-1}r_\pi$ satisfy
--
--   $$\big\|\widehat V^\pi - V^\pi\big\|_\infty \le \frac{6}{1-\gamma}\sqrt{\frac{\beta_1}{N(1-\gamma)}}.$$
--
--   The lemma does not require $\pi$ to be independent of the data; it is the deterministic core of the high-probability bounds for data-dependent policies.
--
--   **Formalization Note** Stated for an arbitrary kernel $\widehat P$ (the proof does not use that it is empirical); $N$ is a natural number. The value functions are the series (1); they equal the resolvent forms of the page.
-- source:
--   arXiv:2005.12900v8, Lemma 2, p. 15, (36)–(38)

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model

namespace BreakingSample.Conservative

open Matrix

theorem lemma_2 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : BreakingSample.Perturbed.IsDiscountedMDP P r γ)
    (Phat : S → A → S → ℝ) (hPhat : FoundationsML.ReinforcementLearning.IsTransitionKernel Phat)
    (π : S → A) (β₁ : ℝ) (hβ₁ : 0 < β₁) (N : ℕ)
    (h37 : ∀ l : ℕ, (l : ℝ) ≤ Real.log (Real.exp 1 / (1 - γ)) → ∀ s,
      |((BreakingSample.Perturbed.policyMatrix Phat π - BreakingSample.Perturbed.policyMatrix P π) *ᵥ BreakingSample.Perturbed.auxV P r γ π l) s|
        ≤ Real.sqrt (β₁ / N) * Real.sqrt (BreakingSample.Perturbed.varPi P π (BreakingSample.Perturbed.auxV P r γ π l) s)
          + β₁ * ‖BreakingSample.Perturbed.auxV P r γ π l‖ / N)
    (hN : 16 * Real.exp 1 ^ 2 / (1 - γ) * β₁ < N) :
    ‖fun s => BreakingSample.Perturbed.value Phat r γ π s - BreakingSample.Perturbed.value P r γ π s‖
      ≤ 6 / (1 - γ) * Real.sqrt (β₁ / (N * (1 - γ))) := by sorry

end BreakingSample.Conservative

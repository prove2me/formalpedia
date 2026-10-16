-- Prove2me | Theorems.Thm_BreakingSample_PolicyEval_lemma_2
-- name    : BreakingSample.PolicyEval.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:01:51.811716+00:00
-- url     : https://prove2.me/theorems/5a5e701f-8775-4631-bbd2-d6f6a41d8520
-- title:
--   Lemma 2, p. 15 — if {V⁽ˡ⁾} obey the Bernstein-type condition (37) and N > 16e²β₁/(1−γ), then ‖V̂^π − V^π‖∞ ≤ (6/(1−γ))√(β₁/(N(1−γ)))
-- statement:
--   Let $(P,r,\gamma)$ be a discounted MDP in the standing setting (finite states and actions, $P$ a transition kernel, $r\in[0,1]$, $0<\gamma<1$), let $\widehat P$ be any transition kernel on the same spaces, $\pi$ a deterministic policy, $\beta_1>0$ and $N$ a natural number. Let $V^{(l)}$ be the auxiliary vectors (36) of $(P,r,\gamma,\pi)$. Suppose that
--   $$
--   \big|(\widehat P_\pi-P_\pi)V^{(l)}\big|\le\sqrt{\frac{\beta_1}{N}}\sqrt{\mathrm{Var}_{P_\pi}\big[V^{(l)}\big]}+\frac{\beta_1\|V^{(l)}\|_\infty}{N}\mathbf 1\qquad\text{for all integers }0\le l\le\log\Big(\frac{e}{1-\gamma}\Big)\tag{37}
--   $$
--   (entrywise) and that $N>16e^2\beta_1/(1-\gamma)$. Then $V^\pi=(I-\gamma P_\pi)^{-1}r_\pi$ and $\widehat V^\pi=(I-\gamma\widehat P_\pi)^{-1}r_\pi$ satisfy
--   $$
--   \big\|\widehat V^\pi-V^\pi\big\|_\infty\le\frac{6}{1-\gamma}\sqrt{\frac{\beta_1}{N(1-\gamma)}} .
--   $$
--
--   The lemma does not require $\pi$ to be independent of $\widehat P$: any policy for which the Bernstein-type condition holds is covered. This is what lets the paper later treat the data-dependent optimal policy of the empirical MDP.
--
--   **Formalization Note** $V^\pi$ and $\widehat V^\pi$ are the value functions of $\pi$ under $P$ and $\widehat P$, which equal the matrix forms above by (27). $\widehat P$ is any transition kernel (on the page it is the empirical kernel), which makes the statement more general. The same lemma is posed in the sibling missions 1 and 2 of this paper series.
-- source:
--   arXiv:2005.12900v8, Lemma 2, (37)–(38), §6.3.1, p. 15; (36), p. 15

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_BreakingSample_Perturbed_Model

namespace BreakingSample.PolicyEval

open FoundationsML.ReinforcementLearning Matrix

/-- Lemma 2 and (37)–(38), arXiv:2005.12900v8, §6.3.1, p. 15: if the auxiliary vectors `V⁽ˡ⁾` of (36)
obey the Bernstein-type condition (37) for all integers `0 ≤ l ≤ log(e/(1−γ))` and
`N > 16e²β₁/(1−γ)`, then `‖V̂^π − V^π‖∞ ≤ 6/(1−γ) √(β₁/(N(1−γ)))`. Here `P̂` (`Phat`) is any
transition kernel and `π` may depend on it. -/
theorem lemma_2 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : BreakingSample.Perturbed.IsDiscountedMDP P r γ)
    (Phat : S → A → S → ℝ) (hPhat : IsTransitionKernel Phat)
    (π : S → A) (β₁ : ℝ) (hβ₁ : 0 < β₁) (N : ℕ)
    (h37 : ∀ l : ℕ, (l : ℝ) ≤ Real.log (Real.exp 1 / (1 - γ)) → ∀ s,
      |((BreakingSample.Perturbed.policyMatrix Phat π - BreakingSample.Perturbed.policyMatrix P π) *ᵥ BreakingSample.Perturbed.auxV P r γ π l) s|
        ≤ Real.sqrt (β₁ / N) * Real.sqrt (BreakingSample.Perturbed.varPi P π (BreakingSample.Perturbed.auxV P r γ π l) s)
          + β₁ * ‖BreakingSample.Perturbed.auxV P r γ π l‖ / N)
    (hN : 16 * Real.exp 1 ^ 2 / (1 - γ) * β₁ < N) :
    ‖fun s => BreakingSample.Perturbed.value Phat r γ π s - BreakingSample.Perturbed.value P r γ π s‖
      ≤ 6 / (1 - γ) * Real.sqrt (β₁ / (N * (1 - γ))) := by sorry

end BreakingSample.PolicyEval

-- Prove2me | Theorems.Thm_BreakingSample_PolicyEval_eq_80
-- name    : BreakingSample.PolicyEval.eq_80
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:01:48.076974+00:00
-- url     : https://prove2.me/theorems/115d27e6-fdfd-463a-9591-0e684bf21c21
-- title:
--   (80), p. 26 — under the Bernstein-type condition (75), ‖V̂^π − V^π‖∞ ≤ γβ₁‖V^π‖∞/((1−γ)N) + 4γ√(β₁/N)‖(I−γP_π)⁻¹√Var_{P_π}[V^π]‖∞
-- statement:
--   Let $(P,r,\gamma)$ be a discounted MDP in the standing setting (finite states and actions, $P$ a transition kernel, $r\in[0,1]$, $0<\gamma<1$), let $\widehat P$ be any transition kernel on the same spaces, $\pi$ a deterministic policy, $\beta_1>0$ and $N$ a natural number. Let $V^{(l)}$ be the auxiliary vectors (36) of $(P,r,\gamma,\pi)$ and write $\widehat P_\pi(s,s')=\widehat P(s'\mid s,\pi(s))$. Suppose that the Bernstein-type condition
--   $$
--   \big|(\widehat P_\pi-P_\pi)V^{(l)}\big|\le\sqrt{\frac{\beta_1}{N}}\sqrt{\mathrm{Var}_{P_\pi}\big[V^{(l)}\big]}+\frac{\|V^{(l)}\|_\infty\beta_1}{N}\mathbf 1\tag{75}
--   $$
--   holds entrywise for every integer $l$ with $0\le l\le\log\frac{e}{1-\gamma}$, and that $N\ge 16e^2\beta_1/(1-\gamma)$. Then the values $V^\pi$ and $\widehat V^\pi$ of $\pi$ under $P$ and under $\widehat P$ satisfy
--   $$
--   \big\|\widehat V^\pi-V^\pi\big\|_\infty\le\frac{\gamma\beta_1}{(1-\gamma)N}\|V^\pi\|_\infty+4\gamma\sqrt{\frac{\beta_1}{N}}\Big\|(I-\gamma P_\pi)^{-1}\sqrt{\mathrm{Var}_{P_\pi}[V^\pi]}\Big\|_\infty .
--   $$
--
--   This is the deterministic, instance-dependent core of the policy-evaluation analysis: all randomness enters only through the condition (75).
--
--   **Formalization Note** On the page $\widehat P$ is the empirical kernel; the statement here holds for any transition kernel $\widehat P$, which is what the argument uses. The page sets $m=\log(e/(1-\gamma))$ and requires (75) for $0\le l\le m$; here $l$ ranges over the integers not exceeding $\log(e/(1-\gamma))$.
-- source:
--   arXiv:2005.12900v8, (75), App. B.1, p. 25; (80), p. 26

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_BreakingSample_Perturbed_Model

namespace BreakingSample.PolicyEval

open FoundationsML.ReinforcementLearning Matrix

/-- (80), arXiv:2005.12900v8, App. B.1, p. 26, under the Bernstein-type condition (75), p. 25, for all
integers `0 ≤ l ≤ log(e/(1−γ))`: the instance-dependent bound
`‖V̂^π − V^π‖∞ ≤ γβ₁/((1−γ)N) ‖V^π‖∞ + 4γ√(β₁/N) ‖(I − γP_π)⁻¹ √Var_{P_π}[V^π]‖∞`
once `N ≥ 16e²β₁/(1−γ)`. Here `P̂` (`Phat`) is any transition kernel. -/
theorem eq_80 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : BreakingSample.Perturbed.IsDiscountedMDP P r γ)
    (Phat : S → A → S → ℝ) (hPhat : IsTransitionKernel Phat)
    (π : S → A) (β₁ : ℝ) (hβ₁ : 0 < β₁) (N : ℕ)
    (h75 : ∀ l : ℕ, (l : ℝ) ≤ Real.log (Real.exp 1 / (1 - γ)) → ∀ s,
      |((BreakingSample.Perturbed.policyMatrix Phat π - BreakingSample.Perturbed.policyMatrix P π) *ᵥ BreakingSample.Perturbed.auxV P r γ π l) s|
        ≤ Real.sqrt (β₁ / N) * Real.sqrt (BreakingSample.Perturbed.varPi P π (BreakingSample.Perturbed.auxV P r γ π l) s)
          + ‖BreakingSample.Perturbed.auxV P r γ π l‖ * β₁ / N)
    (hN : 16 * Real.exp 1 ^ 2 * β₁ / (1 - γ) ≤ N) :
    ‖fun s => BreakingSample.Perturbed.value Phat r γ π s - BreakingSample.Perturbed.value P r γ π s‖
      ≤ γ * β₁ / ((1 - γ) * N) * ‖BreakingSample.Perturbed.value P r γ π‖
        + 4 * γ * Real.sqrt (β₁ / N)
          * ‖BreakingSample.Perturbed.resolvent P γ π *ᵥ (fun s => Real.sqrt (BreakingSample.Perturbed.varPi P π (BreakingSample.Perturbed.value P r γ π) s))‖ := by sorry

end BreakingSample.PolicyEval

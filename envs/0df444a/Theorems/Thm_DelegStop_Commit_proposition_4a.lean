-- Prove2me | Theorems.Thm_DelegStop_Commit_proposition_4a
-- name    : DelegStop.Commit.proposition_4a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:18.786374+00:00
-- url     : https://prove2.me/theorems/988dc7ff-f2e4-4793-8e35-43c8bb3b047f
-- title:
--   Proposition 4 (a), p. 6325 (PDF 10) — committing beats flexibility iff ĉ_I(k) < c_I < c̄_I(k) and p ≥ (c_h − c_l)/(μ_h − μ_l)
-- statement:
--   Consider the two-round delegated innovation game of §3: in each round the provider exerts effort $\mu \in \{\mu_l,\mu_h\}$ at cost $c_l$ or $c_h$ and produces a solution whose quality has distribution $\Phi_\mu(x) = 1 - \mu e^{-x/k}$; the client pays $p$ when the project stops with a feasible solution and pays $c_I$ to evaluate each solution. Under the **flexible** policy the client decides after round 1 whether to stop; under the **committed** policy it stops at the first feasible solution. The provider chooses its efforts by backward induction, anticipating the client's rule. Let $\Pi^F_1$ and $\Pi^C_1$ be the client's equilibrium expected profits under the two policies. Fix $\mu_l,\mu_h,c_l,c_h$ satisfying the standing assumptions of §3.2 ($0 < \mu_l < \mu_h < 1$, $0 \le c_l < c_h$, $c_h/\mu_h \ge c_l/\mu_l$) and a payment $p > 0$.
--
--   **Proposition 4 (a).** There exist two thresholds $\hat c_I(k)$ and $\bar c_I(k)$ such that for every capability $k > 0$ and every evaluation cost $c_I > 0$,
--   $$\Pi^F_1 < \Pi^C_1 \iff \hat c_I(k) < c_I < \bar c_I(k) \ \text{ and } \ p \ge \frac{c_h - c_l}{\mu_h - \mu_l}.$$
--
--   This is the paper's main result: although flexibility is optimal when the provider's effort is fixed (Lemma 2), with a deadline and strategic effort the client strictly prefers to commit exactly in an intermediate range of evaluation costs, and only if the payment is high enough to make high second-round effort worthwhile.
--
--   **Formalization Note.** Only $T = 2$ is modelled, as in the paper's §4. "Benefits" is strict ($\Pi^F_1 < \Pi^C_1$), matching Figure 2's regions $\Pi^F_1 < \Pi^C_1$ and $\Pi^F_1 \ge \Pi^C_1$. The thresholds are functions of $k$, as on the page; they also depend on the fixed $\mu_l,\mu_h,c_l,c_h,p$, and are chosen before $c_I$ is quantified. The paper restricts to payments "neither too high nor too small" (Lemma A-1 of its Online Appendix, not available here); the statement is posed for every $p > 0$, for which it remains true. $c_I > 0$ is assumed (at $c_I = 0$ the flexible client never stops after round 1). Part (b) of the proposition (monotonicity of the thresholds in $k$) is not formalized.
-- source:
--   Rahmani & Ramachandran, Delegating Innovation Projects with Deadline: Committed vs. Flexible Stopping, Management Science 67(10):6317–6332 (2021), p. 6325 (PDF 10), Proposition 4 (a)

import Mathlib
import Definitions.Def_DelegStop_Commit_Model

namespace DelegStop.Commit

theorem proposition_4a (μl μh cl ch p : ℝ) (hS : EffortStanding μl μh cl ch) (hp : 0 < p) :
    ∃ cHat cBar : ℝ → ℝ, ∀ k : ℝ, 0 < k → ∀ cI : ℝ, 0 < cI →
      (profitF ⟨μl, μh, cl, ch, k⟩ cI p < profitC ⟨μl, μh, cl, ch, k⟩ cI p ↔
        (cHat k < cI ∧ cI < cBar k) ∧ (ch - cl) / (μh - μl) ≤ p) := by sorry

end DelegStop.Commit

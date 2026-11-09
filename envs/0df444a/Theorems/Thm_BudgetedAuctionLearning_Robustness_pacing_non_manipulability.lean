-- Prove2me | Theorems.Thm_BudgetedAuctionLearning_Robustness_pacing_non_manipulability
-- name    : BudgetedAuctionLearning.Robustness.pacing_non_manipulability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:28:15.360484+00:00
-- url     : https://prove2.me/theorems/648ef9b2-3491-4ecb-8def-7ccc8bf038cd
-- title:
--   Theorem 3.4 — pacing non-manipulability (corrected: positive expected learner value)
-- statement:
--   Fix an auction format, first-price or second-price, a Borel probability law $D$ on $[0,1]^2$ for the correlated pair $(v_L,v_O)$, and budgets $\rho_L,\rho_O>0$. Suppose $P[0<v_L<v_O\varepsilon]=0$ for some $\varepsilon>0$ and $E[v_L]>0$. There is a constant $C\ge0$, depending only on these data, such that the following holds for every horizon $T\ge1$, step size $\eta\in(0,1)$, initialization $0\le\lambda^{(1)}\le\rho_L$ and adaptive randomized optimizer that respects her budget $T\rho_O$ with probability one, when the learner bids $\lambda^{(t)}v_L^{(t)}$ under the controller (3):
--
--   $$E\Big[\sum_{t=1}^Tv_O^{(t)}\mathbf 1\{\text{optimizer wins round }t\}\Big]\le\mathrm{OPT}\cdot T+C\Big(T\sqrt\eta+\frac1\eta\Big).$$
--
--   Moreover, for constants $a,b>0$, whenever $aT^{-2/3}\le\eta\le bT^{-2/3}$ and $\eta\in(0,1)$,
--
--   $$E\Big[\sum_{t=1}^Tv_O^{(t)}\mathbf 1\{\text{optimizer wins round }t\}\Big]\le\mathrm{OPT}\cdot T+C\Big(\sqrt b+\frac1a\Big)T^{2/3}.$$
--
--   Here $\mathrm{OPT}$ is the supremum of Optimization Program (4). This is the paper's main result: the learner's simple controller cannot be manipulated beyond the budgeted Stackelberg value, up to a sublinear term.
--
--   **Formalization Note.** The optimizer's bids are not capped by her value, and her objective is value, not value minus payment. The case $E[v_O]=0$ is included. A learner bid of $0$ at $\lambda^{(1)}=0$ is handled at actual bids. The source proof's bound for $\sigma>0$ is $T\,\mathrm{OPT}+\mu\sigma T+\frac\eta\sigma[\rho_L^2+(\frac{\bar\lambda-\eta\rho_L}{1-\eta})^2]dT+\bar\lambda d/\eta$ with $d=(E[v_O]-R^\star)/\rho_L$, which, with $\sigma=\sqrt\eta$, an additional $1$ for a zero-pacing first round and the bound $\text{value}\le T$ when $\eta>1/2$, gives the sufficient coefficient $C=\sqrt2+1+\mu+d(\rho_L^2+4\bar\lambda^2+\bar\lambda)$.
--
--   Differences from the source:
--   - correction: Theorem 3.4 allows $E[v_L]=0$ while OPT is program (4) → hypothesis $0<E[v_L]$; reason: with $D$ the point mass at $(v_L,v_O)=(0,1)$, $\rho_L=\rho_O=1$, $\varepsilon=1$, $\eta=1/2$, $\lambda^{(1)}=1$ every printed assumption holds, yet every learner payment is $0$, so (4) is infeasible and OPT is undefined ($-\infty$), while the optimizer earns $T$ by bidding $1/2$ in second-price
--   - encoding: optimizer strategies that randomize and adapt to earlier values → a seed in an arbitrary measurable space with law $\nu$, independent of the values, and jointly measurable bids in the seed, all earlier value pairs and her current value; reason: this covers every source strategy; the multiplier and earlier bids are functions of this data
--   - encoding: $T$ repeated rounds, 1-based → an i.i.d. infinite product law with 0-based rounds, summing over the first $T$; reason: the first $T$ coordinates have the same law
--   - reading: $O(T\sqrt\eta+1/\eta)$ with footnote 5 → $\exists C\ge0$ chosen after the format, $D$, $\rho_L,\rho_O,\varepsilon$ and before $T,\eta,\lambda^{(1)}$ and the optimizer; reason: footnote 5 says the $O(\cdot)$ hides only budget and value-distribution terms, and the gap witness is part of that data
--   - reading: $\eta=\Theta(T^{-2/3})$ gives $O(T^{2/3})$ → for all $a,b>0$ and all $T$ with $aT^{-2/3}\le\eta\le bT^{-2/3}$, the excess is at most $C(\sqrt b+1/a)T^{2/3}$; reason: this covers every such schedule at each $T$ where its bounds hold, with a coefficient uniform in the optimizer and the initialization
--   - encoding: real-valued OPT and expected accumulated value → an `EReal` benchmark supremum and an `ℝ≥0∞` lower integral for accumulated value; reason: positive learner expectation makes (4) nonempty, and bounded values bound OPT and total value; both are finite on these instances, while an empty benchmark would explicitly give $-\infty$
--   - encoding: randomized fake value $\hat V\in\Delta(\mathbb R_{\ge0}^{[0,1]})$ → Markov kernel from $[0,1]$ to $\mathbb R_{\ge0}$; reason: $U_O,P_O,P_L$ depend only on the conditional bid law given $v_O$; every measurable random map yields such a kernel and every kernel on these standard Borel spaces is realized by one
--   - encoding: the fake-value normalization in §§3 and 5, also written at $\lambda=0$ → actual-bid auction rules in the goal, including $\lambda^{(1)}=0$, and normalized allocations only in auxiliary quantities; reason: normalizing actual bids requires positive pacing; a zero initial pacing round has value at most 1 and next multiplier $\eta\rho_L>0$, so its possible extra value is absorbed by $1/\eta$ without removing this source initialization
-- source:
--   Fikioris, Tardos, Sivan, STOC 2027 submission #310 (October 2026), Theorem 3.4 and footnote 5, printed pp. 9–10 (PDF pp. 10–11); proof printed p. 19 (PDF p. 20)

import Mathlib
import Definitions.Def_BudgetedAuctionLearning_Robustness_Benchmark
import Definitions.Def_BudgetedAuctionLearning_Robustness_RepeatedRun
open MeasureTheory ProbabilityTheory
open scoped unitInterval NNReal ENNReal

namespace BudgetedAuctionLearning.Robustness

/-- Theorem 3.4, printed pp. 9–10 (PDF pp. 10–11), corrected by `0 < E[v_L]`. The constant `C` comes
before the horizon, the step size, the initialization and the optimizer. -/
theorem pacing_non_manipulability (fmt : AuctionFormat) (D : Measure ValuePair) [IsProbabilityMeasure D]
    (ρL ρO ε : ℝ) (hρL : 0 < ρL) (hρO : 0 < ρO) (hε : 0 < ε) (hgap : ValueGap D ε)
    (hEL : 0 < meanLearnerValue D) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ (T : ℕ) (η lam₁ : ℝ), 0 < T → 0 < η → η < 1 → 0 ≤ lam₁ → lam₁ ≤ ρL →
        ∀ (S : Type) [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
          (π : OptimizerPolicy S), OptimizerBudgetFeasible fmt D ρL ρO η lam₁ ν π T →
          ((expectedOptimizerValue fmt D ρL η lam₁ ν π T : ℝ≥0∞) : EReal) ≤
            ((T : ℝ) : EReal) * bseValue fmt D ρL ρO +
              ((C * ((T : ℝ) * Real.sqrt η + 1 / η) : ℝ) : EReal)) ∧
      (∀ a b : ℝ, 0 < a → 0 < b → ∀ (T : ℕ) (η lam₁ : ℝ), 0 < T → 0 < η → η < 1 →
        a * (T : ℝ) ^ (-(2 / 3) : ℝ) ≤ η → η ≤ b * (T : ℝ) ^ (-(2 / 3) : ℝ) → 0 ≤ lam₁ → lam₁ ≤ ρL →
        ∀ (S : Type) [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
          (π : OptimizerPolicy S), OptimizerBudgetFeasible fmt D ρL ρO η lam₁ ν π T →
          ((expectedOptimizerValue fmt D ρL η lam₁ ν π T : ℝ≥0∞) : EReal) ≤
            ((T : ℝ) : EReal) * bseValue fmt D ρL ρO +
              ((C * (Real.sqrt b + 1 / a) * (T : ℝ) ^ ((2 : ℝ) / 3) : ℝ) : EReal)) := by sorry

end BudgetedAuctionLearning.Robustness

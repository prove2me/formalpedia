-- Prove2me | Theorems.Thm_ApproxOptRL_CPI_cpi_guarantee
-- name    : ApproxOptRL.CPI.cpi_guarantee
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:46:22.800326+00:00
-- url     : https://prove2.me/theorems/a6a9eacc-5f0f-4879-a8a9-c835a254f789
-- title:
--   Theorem 4.4 — w.p. $\ge 1-\delta$, CPI improves $\eta_\mu$ at every update, stops within $72R^2/\varepsilon^2$ updates, returns $\pi$ with $\mathrm{OPT}(\mathbb A_{\pi,\mu})<2\varepsilon$
-- statement:
--   Consider a finite MDP with nonempty state set $S$, nonempty action set $A$, transition probabilities $P(s';s,a)$, rewards $\mathcal R(s,a)\in[0,R]$ with $R>0$, discount factor $0\le\gamma<1$, and restart distribution $\mu$. Fix $\varepsilon>0$, $\delta>0$, an $\varepsilon$-greedy policy chooser $G_\varepsilon$ (Definition 4.3) and an initial policy $\pi_0$.
--
--   Run conservative policy iteration (§5): in loop $j = 0,1,\dots$ with current policy $\pi_j$, the chooser returns $\pi'_j = G_\varepsilon(\pi_j)$, a random estimate $\hat{\mathbb A}_j$ of $\mathbb A_{\pi_j,\mu}(\pi'_j)$ is formed; if $\hat{\mathbb A}_j<\frac{2\varepsilon}3$ the run stops and returns $\pi_j$, and otherwise $\pi_{j+1} = (1-\alpha_j)\pi_j + \alpha_j\pi'_j$ with $\alpha_j = \frac{(1-\gamma)(\hat{\mathbb A}_j-\varepsilon/3)}{4R}$.
--
--   Step (2) of the algorithm uses enough $\mu$-restarts that each estimate is $\frac\varepsilon3$-accurate except with small probability. This is assumed in the form: with $N=\lfloor 72R^2/\varepsilon^2\rfloor$, for every $j$,
--   $$\Pr\Big(\text{loop } j \text{ is reached and } \big|\hat{\mathbb A}_j - \mathbb A_{\pi_j,\mu}(\pi'_j)\big| \ge \tfrac\varepsilon3\Big) \le \frac{\delta}{N+1}.$$
--
--   **Theorem 4.4.** With probability at least $1-\delta$, conservative policy iteration
--
--   1. improves $\eta_\mu$ with every policy update: $\eta_\mu(\pi_{j+1}) > \eta_\mu(\pi_j)$ for every update $j$;
--   2. ceases after at most $72\frac{R^2}{\varepsilon^2}$ policy updates, that is, it stops in a loop $\tau$ with $\tau\le 72R^2/\varepsilon^2$; and
--   3. returns a policy $\pi=\pi_\tau$ such that
--   $$\mathrm{OPT}(\mathbb A_{\pi,\mu}) < 2\varepsilon.$$
--
--   This is the main guarantee of the paper: with a greedy chooser of accuracy $\varepsilon$, a number of iterations polynomial in $R/\varepsilon$ and independent of the size of the state space yields a policy close to the "break point" of the chooser.
--
--   **Formalization Note** The run is pathwise: the estimates are arbitrary real random variables $\hat{\mathbb A}_j(\omega)$ on a probability space, and $\Pr$ of a non-measurable set is its outer measure, so no measurability of the estimates is assumed. The conclusion is stated as "the failure event has probability at most $\delta$". Two disclosed deviations from the printed statement: (a) the paper's (ii) says "at most $72R^2/\varepsilon^2$ calls to $G_\varepsilon$", but its proof bounds the number of policy **updates**, and the run calls $G_\varepsilon$ once more than it updates (the final call precedes the STOP); (ii) is therefore stated for updates, equivalently at most $72R^2/\varepsilon^2+1$ calls. (b) The per-loop failure budget is $\delta/(N+1)$ for the $N+1$ loops that may be reached, instead of the proof's union bound over $72R^2/\varepsilon^2$ loops, for the same off-by-one reason. The estimation procedure itself (Hoeffding's inequality (5.1)) is not formalized; its role is taken by the accuracy hypothesis. The step size is clipped at $1$, which never binds on the accuracy event.
-- source:
--   Kakade, Langford, Approximately Optimal Approximate Reinforcement Learning, ICML 2002, p. 5, Theorem 4.4 (algorithm p. 6, §5; proof p. 8, appendix §8)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_ApproxOptRL_Shared_Model
import Definitions.Def_ApproxOptRL_CPI_PolicyAdvantage
import Definitions.Def_ApproxOptRL_CPI_Algorithm
open ApproxOptRL.Shared
open FoundationsML.ReinforcementLearning MeasureTheory

namespace ApproxOptRL.CPI

/-- **Theorem 4.4** (Kakade–Langford, ICML 2002, p. 5; proof p. 8). With probability at least
`1 - δ`, conservative policy iteration (§5, p. 6), started from any policy `π₀` and run with an
`ε`-greedy policy chooser `G` (Definition 4.3):
(i) improves `η_μ` (strictly) with every policy update,
(ii) stops after at most `72 R²/ε²` policy updates, and
(iii) returns a policy `π` with `OPT(𝔸_{π,μ}) < 2ε`.

The run is driven by random estimates `est j ω` (the `Â` of step (2) in loop `j`, on the
probability space `(Ω, Pr)`). Step (2) is encoded by its guarantee: for each loop `j`, the
event "loop `j` is reached and `|Â - 𝔸_{π,μ}(π')| ≥ ε/3`" has probability at most
`δ/(N + 1)`, `N = ⌊72R²/ε²⌋`. The failure event is the complement of: there is a `τ`, the loop
in which the run stops, with `τ ≤ 72R²/ε²`, strict improvement of `η_μ` at each of the `τ`
updates, and `OPT(𝔸_{π_τ,μ}) < 2ε` for the returned policy `π_τ`.

Printed slip (disclosed): the paper's (ii) counts "calls to `G_ε`"; the proof (p. 8) bounds
the number of policy **updates**, and the run makes one more call to `G_ε` than updates, so
(ii) is stated for updates (equivalently: at most `72R²/ε² + 1` calls). -/
theorem cpi_guarantee {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]
    [Nonempty S] [Nonempty A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (r : S → A → ℝ) (R : ℝ) (hR : 0 < R) (hr : ∀ s a, 0 ≤ r s a ∧ r s a ≤ R)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (μ : S → ℝ) (hμ : IsStateDist μ)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (G : (S → A → ℝ) → (S → A → ℝ)) (hG : IsGreedyChooser P r γ μ ε G)
    (π₀ : S → A → ℝ) (hπ₀ : IsPolicy π₀)
    {Ω : Type} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (est : ℕ → Ω → ℝ)
    (hest : ∀ j : ℕ,
      Pr {ω | (∀ i < j, 2 * ε / 3 ≤ est i ω) ∧
        ε / 3 ≤ |est j ω - policyAdvantage P r γ (cpiPolicy γ R ε G π₀ (fun i => est i ω) j) μ
          (G (cpiPolicy γ R ε G π₀ (fun i => est i ω) j))|}
        ≤ ENNReal.ofReal (δ / ((⌊72 * R ^ 2 / ε ^ 2⌋₊ : ℝ) + 1))) :
    Pr {ω | ¬ ∃ τ : ℕ, (τ : ℝ) ≤ 72 * R ^ 2 / ε ^ 2 ∧
        (∀ j < τ, 2 * ε / 3 ≤ est j ω) ∧ est τ ω < 2 * ε / 3 ∧
        (∀ j < τ, eta P r γ (cpiPolicy γ R ε G π₀ (fun i => est i ω) j) μ <
          eta P r γ (cpiPolicy γ R ε G π₀ (fun i => est i ω) (j + 1)) μ) ∧
        optPolicyAdvantage P r γ (cpiPolicy γ R ε G π₀ (fun i => est i ω) τ) μ < 2 * ε}
      ≤ ENNReal.ofReal δ := by sorry

end ApproxOptRL.CPI

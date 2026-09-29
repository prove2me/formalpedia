-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_travel_time_le_of_lyapunov_drift
-- name    : BanditAlgorithm.mdp_travel_time_le_of_lyapunov_drift
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-06T04:12:41.703369+00:00
-- url     : https://prove2.me/theorems/f454e264-e1e5-4ee0-9856-010484e93ada
-- title:
--   Foster--Lyapunov drift bound for MDP travel time: a nonnegative $V$ with one-step drift $\le -1$ off the target bounds the hitting time by $V(\mathrm{src})$
-- statement:
--   **Statement.** Let $M$ be a finite MDP, $f$ a memoryless deterministic policy, and $V : S \to \mathbb{R}$ nonnegative. If at every state $s \ne \mathrm{tgt}$ the one-step drift of $V$ under the action $f(s)$ is at most $-1$,
--   $$\sum_{s'} P_{f(s)}(s, s')\,V(s') + 1 \;\le\; V(s),$$
--   then the travel time from $\mathrm{src}$ to $\mathrm{tgt}$ under $f$ satisfies
--   $$\mathbb{E}^{f}\bigl[\min\{t \ge 1 : S_t = \mathrm{tgt}\} \mid S_1 = \mathrm{src}\bigr] - 1 \;\le\; V(\mathrm{src}).$$
--
--   This is the standard Foster--Lyapunov (drift) criterion for hitting times, in exactly the form the diameter of an MDP needs: the diameter is a minimum over memoryless deterministic policies of the travel time, so a single $f$ together with a single $V$ certifies an upper bound on it. Mathlib has no hitting-time drift criterion, and the statement is phrased directly against the finite-horizon-marginal encoding of the travel time, so no separate theory of stopping times is required.
--
--   **Proof.** Write $q_k$ for the probability that none of the first $k+1$ states is $\mathrm{tgt}$, so that the travel time is $\sum_{k \ge 0} q_k$, and let
--   $$u_k = \mathbb{E}\bigl[\mathbf{1}\{\text{survived through round } k+1\}\;V(S_{k+1})\bigr].$$
--   Conditioning on one more round and using the drift hypothesis at the last state, which is legitimate precisely because on the survival event that state is not $\mathrm{tgt}$, gives $u_{k+1} + q_k \le u_k$; summing telescopes to $\sum_{k<N} q_k \le u_0 - u_N \le u_0 \le V(\mathrm{src})$, and letting $N \to \infty$ finishes, the tsum in $[0,\infty]$ being the supremum of its partial sums.
--
--   One point deserves mention because it is where memorylessness is used and where a purely formal argument would break. The drift hypothesis constrains the row $P_{f(s)}(s, \cdot)$, but the transition actually taken out of round $k+1$ uses the action *recorded in the trajectory*, and that the two agree is only an almost-sure statement. The proof therefore carries the indicator of the event "every recorded action is $f$ of the recorded state" alongside the survival indicator; that event has probability one under the memoryless deterministic policy, by an induction on the horizon whose step is the observation that the policy's selection kernel is a Dirac mass, and the extra indicator is removed at the end at no cost.
-- source:
--   Standard Foster-Lyapunov drift criterion for hitting times; see e.g. Meyn & Tweedie, "Markov Chains and Stochastic Stability" (2nd ed., CUP 2009), Theorem 11.3.4, and Bremaud, "Markov Chains" (Springer 1999), Chapter 5. Used here to bound the diameter of Lattimore & Szepesvari, "Bandit Algorithms" (CUP 2020), Definition 38.1, for the composite MDP of Jaksch, Ortner & Auer, JMLR 11 (2010), Section 6, Figure 4.

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_FiniteMDPLearning

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.mdp_travel_time_le_of_lyapunov_drift {S A : ℕ} (M : FiniteMDP S A)
    (f : Fin S → Fin A) (src tgt : Fin S) (V : Fin S → ℝ)
    (hV0 : ∀ s, 0 ≤ V s)
    (hdrift : ∀ s, s ≠ tgt → (∑ s', (M.P s (f s) s' : ℝ) * V s') + 1 ≤ V s) :
    mdpTravelTime M f src tgt ≤ ENNReal.ofReal (V src) := by
  sorry

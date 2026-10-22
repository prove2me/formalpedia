-- Prove2me | Theorems.Thm_FollowCrowd_Inference_proposition_2
-- name    : FollowCrowd.Inference.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:22.817186+00:00
-- url     : https://prove2.me/theorems/24d6b987-5ca0-4c16-a927-9d2f9245d9dd
-- title:
--   Proposition 2, p. 10 (corrected) — FTC: JP^U(v+δ) > JP^U(v) for some v ∈ (0, N̄), δ > 0 iff R/C lies in an inference interval for some n ∈ {1, …, N̄−1}
-- statement:
--   **Follow the crowd (corrected).** Assume $\mu_H > \mu_L > 0$, $\gamma\in(0,1)$, $\lambda > 0$, $C > 0$ and $R > C/\mu_L$, and let $\bar N = \lfloor R\mu_H/C\rfloor$. The other customers use the threshold profile $p^-(v)$: they join at queue lengths $\le\lfloor v\rfloor$, join with probability $v - \lfloor v\rfloor$ at $\lfloor v\rfloor + 1$, and balk above. The tagged customer infers the capacity from the queue length by Bayes' rule, with belief $\theta_n(v)$, and joins at queue length $n$ iff $n = 0$ or $u(n,v) = R - C(n+1)E(\theta_n(v)) \ge 0$, where $E(\theta) = \theta/\mu_H + (1-\theta)/\mu_L$. Let $JP^U(v)$ be her ex-ante probability of joining. Then there exist $v\in(0,\bar N)$ and $\delta > 0$ with
--   $$JP^U(v+\delta) > JP^U(v)$$
--   if and only if, for some $n\in\{1,2,\dots,\bar N-1\}$,
--   $$(n+1)\,E\bigl(\theta_n(\bar N-1)\bigr) \le \frac RC < (n+1)\,E\bigl(\theta_n((n-2)^+)\bigr).$$
--
--   The ex-ante joining probability can increase with the other customers' willingness to join (follow-the-crowd behaviour) exactly when the reward–cost ratio falls in one of these inference intervals: at the state $n$, rising joining by others raises the belief of fast service enough to flip the tagged customer from balking to joining, while state $n$ is still reachable.
--
--   **Formalization Note** The paper prints the condition as $(n+1)E(\theta_n(\bar N-1)) < R/C < (n+1)E(\theta_n(0))$. As printed, the "if" direction is false. Counterexample: $\lambda = 3$, $\mu_H = 3$, $\mu_L = 2$, $R = 5/2$, $C = 1$, $\gamma = 3/4$, so $\rho_H = 1$, $\rho_L = 3/2$, $\bar N = 7$; at $n = 5$, $u(5,0) = -41/242 < 0$ and $u(5,6) = 3713/17794 > 0$, so the printed condition holds, but already $u(5,3) = 17/1654 > 0$: the tagged customer starts joining at state 5 for a threshold $v < 3$, where state 5 has probability zero under $p^-(v)$, so the jump in her strategy adds nothing, and $JP^U$ is non-increasing on $(0,7)$. State $n$ has zero probability under $p^-(v)$ exactly when $v\le n-2$, so the upper bound uses the belief at $(n-2)^+$ instead of $0$ (the two coincide for $n\in\{1,2\}$). The left inequality is weak because of Assumption 1's tie-break: when $u(n,\bar N-1) = 0$ the customer joins at $v = \bar N - 1$ and the jump still occurs. In Lean $(n-2)^+$ and $\bar N - 1$ are natural-number subtractions, cast to reals; the belief is (A-1), defined at every state.
-- source:
--   Yang, Shang & Liu, Follow the crowd with uncertain service capacity, SSRN 4159035 (version of June 24, 2022), p. 10, Proposition 2 (corrected; see Formalization Note); proof: Online Appendix p. 1 (PDF 25)

import Mathlib
import Definitions.Def_FollowCrowd_Inference_Model

namespace FollowCrowd.Inference

theorem proposition_2 (P : Params) (hP : P.Standing) :
    (∃ v ∈ Set.Ioo (0 : ℝ) (Nbar P), ∃ δ > 0, JPV P v < JPV P (v + δ)) ↔
      ∃ n ∈ Finset.Icc 1 (Nbar P - 1),
        ((n : ℝ) + 1) * meanSojourn P (thetaV P ((Nbar P - 1 : ℕ) : ℝ) n) ≤ P.R / P.C ∧
          P.R / P.C < ((n : ℝ) + 1) * meanSojourn P (thetaV P ((n - 2 : ℕ) : ℝ) n) := by sorry

end FollowCrowd.Inference

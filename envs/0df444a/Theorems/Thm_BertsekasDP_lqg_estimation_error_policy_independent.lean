-- Prove2me | Theorems.Thm_BertsekasDP_lqg_estimation_error_policy_independent
-- name    : BertsekasDP.lqg_estimation_error_policy_independent
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-08T00:38:07.981224+00:00
-- url     : https://prove2.me/theorems/fde27ca4-e09c-4f5c-a0d8-11e63736f9f3
-- title:
--   Estimation error is policy-independent (Lemma 5.2.1)
-- statement:
--   **Lemma 5.2.1 (the estimation error does not depend on the policy).** In the linear-quadratic problem with imperfect state information, let $\pi$ and $\pi'$ be any two information-feedback policies, and let $x_k^\pi$, $\hat x_k^\pi = \mathbb{E}[x_k \mid I_k]$ denote the state and its least-squares estimate under $\pi$. Then for every stage $k \le N$ and every outcome of positive probability,
--
--   $$x_k^{\pi} - \hat x_k^{\pi} \;=\; x_k^{\pi'} - \hat x_k^{\pi'} .$$
--
--   That is, the estimation error is the same realization by realization, whichever controls were applied.
--
--   The reason is that the controls are a known function of the measurement history, so they shift the state and the measurements by a quantity that is fully known at the time of estimation and cancels in the error. The consequence is the one the source needs: in the dynamic programming recursion the quadratic estimation-error term is a function $M_k(I_k)$ of the information alone, so it may be pulled out of the minimization over $u_k$. Once that term is out of the way, what remains is the perfect-information problem with $x_k$ replaced by $\mathbb{E}[x_k \mid I_k]$ — which is exactly certainty equivalence.
--
--   **Formalization Note** This is the pointwise (per-outcome) form of the source's statement, which asserts the existence of a function $M_k$ of the information vector; the pointwise version implies it and is what the dynamic programming argument consumes. The hypothesis that the outcome has nonzero probability guarantees both conditional expectations have nonzero denominators, excluding the junk value $0$ of conditional expectation on null events.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Lemma 5.2.1

import Mathlib
import Definitions.Def_BertsekasLQGModel

namespace BertsekasDP

theorem lqg_estimation_error_policy_independent {n m q : ℕ}
    {Ω₀ ΩW ΩV : Type} [Fintype Ω₀] [Fintype ΩW] [Fintype ΩV]
    (M : BertsekasLQGModel n m q Ω₀ ΩW ΩV)
    (π π' : List (Fin q → ℝ) → Fin m → ℝ) (k : ℕ) (hk : k ≤ M.N)
    (ω : BertsekasLQGSample M) (hω : BertsekasLQGProb M ω ≠ 0) :
    (BertsekasLQGTraj M π k ω).1 - BertsekasLQGEstimate M π k ω =
      (BertsekasLQGTraj M π' k ω).1 - BertsekasLQGEstimate M π' k ω := by sorry

end BertsekasDP

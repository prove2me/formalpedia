-- Prove2me | Theorems.Thm_BertsekasDP_lqg_certainty_equivalence
-- name    : BertsekasDP.lqg_certainty_equivalence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-08T00:37:32.782008+00:00
-- url     : https://prove2.me/theorems/ed86494c-2921-482f-b58e-bd3899a692e0
-- title:
--   Certainty equivalence / separation theorem (§5.2)
-- statement:
--   **The separation theorem / certainty equivalence principle** (Bertsekas, Vol. I, §5.2). Consider the linear-quadratic problem with imperfect state information: dynamics $x_{k+1} = A_k x_k + B_k u_k + w_k$, measurements $z_k = C_k x_k + v_k$, quadratic cost with $Q_k \succeq 0$ and $R_k \succ 0$, and independent finitely supported zero-mean disturbances. Let $L_k$ be the gain matrices of the corresponding **deterministic** linear-quadratic problem, and let $\hat x_k = \mathbb{E}[x_k \mid I_k]$ be the least-squares estimate of the state given the measurement history $I_k = (z_0,\dots,z_k)$.
--
--   Suppose a policy $\pi^*$ satisfies, along its own closed-loop trajectories and at every stage $k < N$,
--
--   $$\pi^*(I_k) \;=\; L_k \, \mathbb{E}\bigl[x_k \mid I_k\bigr].$$
--
--   Then $\pi^*$ is optimal:
--
--   $$J(\pi^*) \;\le\; J(\pi) \qquad \text{for every information-feedback policy } \pi .$$
--
--   The optimal controller therefore **separates** into two independently designed parts: an *estimator*, which produces $\mathbb{E}[x_k \mid I_k]$ and is the solution of a pure estimation problem in which no control takes place, and an *actuator*, which multiplies that estimate by the gain $L_k$ that would be used if the state were observed exactly. Remove this theorem and the entire LQG design methodology — Kalman filter feeding an LQR gain — loses its warrant. Notably no Gaussian assumption is required: independence and zero mean suffice.
--
--   **Formalization Note** The hypothesis is imposed only on outcomes of positive probability, where the conditional expectation is genuine rather than the junk value $0$; on measurement histories that never occur, the policy is unconstrained and does not affect the cost. The competitor class is *all* functions from measurement lists to controls, with no linearity or measurability restriction. The inequality is not strict.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Section 5.2 (separation theorem / certainty equivalence)

import Mathlib
import Definitions.Def_BertsekasLQGModel

open Matrix

namespace BertsekasDP

theorem lqg_certainty_equivalence {n m q : ℕ} {Ω₀ ΩW ΩV : Type}
    [Fintype Ω₀] [Fintype ΩW] [Fintype ΩV]
    (M : BertsekasLQGModel n m q Ω₀ ΩW ΩV)
    (πstar : List (Fin q → ℝ) → Fin m → ℝ)
    (hstar : ∀ k < M.N, ∀ ω : BertsekasLQGSample M,
      BertsekasLQGProb M ω ≠ 0 →
      πstar ((BertsekasLQGTraj M πstar k ω).2) =
        BertsekasLQGGain M k *ᵥ BertsekasLQGEstimate M πstar k ω) :
    ∀ π : List (Fin q → ℝ) → Fin m → ℝ,
      BertsekasLQGCost M πstar ≤ BertsekasLQGCost M π := by sorry

end BertsekasDP

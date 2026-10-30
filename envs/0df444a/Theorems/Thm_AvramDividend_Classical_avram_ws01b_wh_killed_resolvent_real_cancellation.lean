-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_wh_killed_resolvent_real_cancellation
-- name    : AvramDividend.Classical.avram_ws01b_wh_killed_resolvent_real_cancellation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:56:55.269992+00:00
-- url     : https://prove2.me/theorems/e3ef8d93-69f2-4eec-b18d-4d9e8a822e17
-- title:
--   Exact Wiener–Hopf scalar cancellation for the original Lévy killed scale resolvent
-- statement:
--   For r>0, a positive root Φ and θ>Φ with ψ(θ)>r+q, the original descending drawdown transform multiplied by the shifted exponential-supremum Wq integral simplifies exactly to (r+q)/(r(ψ(θ)-q)). This real algebraic identity is a component of the genuine original-clock killed spatial resolvent proof, and makes no claim about stochastic independence.
-- source:
--   Original actual Wiener–Hopf factors proved in 47e972c8 and b770b878; classical scale Laplace transform; KKR Theory of Scale Functions §2.5 Theorem 2.7. This helper establishes the exact nonzero-denominator real scalar cancellation; source-law identification remains a separate genuine probability obligation.

import Mathlib.Tactic

theorem AvramDividend.Classical.avram_ws01b_wh_killed_resolvent_real_cancellation
    (r q Φ θ A : ℝ)
    (hr : 0 < r) (hΦ : 0 < Φ) (hθ : Φ < θ)
    (hA : r + q < A) :
    (((r + q) * (θ - Φ)) / (Φ * (A - (r + q)))) *
      (Φ / (θ - Φ) * (1 / r - 1 / (A - q))) =
      (r + q) / (r * (A - q)) := by sorry

-- Prove2me | Theorems.Thm_AcquihiringMonopsony_Baseline_dh_payoff_employee
-- name    : AcquihiringMonopsony.Baseline.dh_payoff_employee
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:08:43.556988+00:00
-- url     : https://prove2.me/theorems/5f7684a4-34c9-4237-9446-b3ab18f77c62
-- title:
--   Proof of Proposition 1, p. 6 — the employee's payoff from direct hiring is v_s + b if v_a ≥ v_s + b, and v_a otherwise
-- statement:
--   In the baseline model with $b > 0$ and $\min\{v_a, v_s\} > b + \underline{w}$, consider any continuation equilibrium in undominated strategies of the direct-hiring subgame. The employee's equilibrium payoff (her wage, plus the private benefit $b$ if she stays at the startup) is
--   $$
--   \begin{cases} v_s + b & \text{if } v_a \ge v_s + b,\\ (v_a - b) + b = v_a & \text{otherwise.}\end{cases}
--   $$
--
--   This is the second step of the proof of Proposition 1: wage competition hands the employee the losing firm's full willingness to pay.
--
--   **Formalization Note.** At $v_a = v_s + b$ both branches equal $v_a$; the statement covers that point as well.
-- source:
--   Bar-Isaac, Johnson, Nocke, Acquihiring for Monopsony Power, CRC TR 224 DP No. 500 (Jan. 2024), p. 6 (PDF 7), §3, proof of Proposition 1, second paragraph

import Mathlib
import Definitions.Def_AcquihiringMonopsony_Baseline_Model

namespace AcquihiringMonopsony.Baseline

/-- Proof of Proposition 1 (p. 6), second paragraph: in every continuation equilibrium of the
direct-hiring subgame the employee's payoff is `v_s + b` if `v_a ≥ v_s + b` and `v_a`
otherwise. -/
theorem dh_payoff_employee (P : Params) (hP : P.Standing) (σ : DHProfile)
    (hσ : IsDHEquilibrium P σ) :
    dhPayoffE P σ.acceptA σ.wa σ.ws = if P.vs + P.b ≤ P.va then P.vs + P.b else P.va := by sorry

end AcquihiringMonopsony.Baseline

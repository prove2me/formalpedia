-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_dyadic_ceiling_prefix_drawdown_reward_joint_measurable
-- name    : AvramDividend.Classical.avram_ws01e_b_dyadic_ceiling_prefix_drawdown_reward_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T17:20:30.630064+00:00
-- url     : https://prove2.me/theorems/46658681-fd81-4534-b098-1fe3d7c69f6b
-- title:
--   Full product-Pi measurability of dyadic ceiling sampled drawdown exponential test using countable prefix records
-- statement:
--   For a fixed countable deterministic sample schedule r_i, dyadic ceiling resolution n, and β real, define q_n(u)=ceil(2^n u)/2^n and the countably sampled nonnegative record R_n(u,f)=toReal(sup_i if r_i≤q_n(u) then ofReal(f(r_i)) else 0). Then the full drawdown Laplace surrogate H_n(u,f)=ofReal exp(-β(R_n(u,f)-f(q_n(u)))) is jointly measurable on Borel NNReal observation time × unrestricted Pi measurable path space, without falsely asserting variable-time evaluation f(u) to be product-measurable. This is the exact mathematical observability condition for applying the canonically Proved genuine random-terminal upper-record full-path regeneration f5788ba0 to exponentially weighted drawdown tests. The endpoint component is already Proved under UUID 7789c1eb; prefix records are a countable iSup of measurable fixed-coordinate evaluations with measurable time-threshold fibres. This theorem asserts measurability only; actual pathwise recovery of the continuous supremum along dense schedules and bounded convergence remain separate obligations.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2013) §2.1 Wiener–Hopf path regeneration; Proved genuine Qp regeneration f5788ba0-5ca1-4ac9-ad2a-8c147d4c369c and measurable dyadic ceiling endpoint 7789c1eb-8bbd-480d-92de-c4d48bf18202.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_dyadic_ceiling_prefix_drawdown_reward_joint_measurable
    (samples : ℕ → ℝ≥0) (β : ℝ) (n : ℕ) :
    Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) =>
      let r : ℝ≥0 :=
        (Nat.ceil ((z.1 : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n
      ENNReal.ofReal (Real.exp
        (-β * ((⨆ i : ℕ, if samples i ≤ r then
          ENNReal.ofReal (z.2 (samples i)) else 0).toReal - z.2 r)))) := by sorry

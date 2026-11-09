-- Prove2me | Theorems.Thm_CoordBoundaries_Throughput_global_job_rounding
-- name    : CoordBoundaries.Throughput.global_job_rounding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:48:31.595228+00:00
-- url     : https://prove2.me/theorems/67aa8d31-066c-49c0-8b66-e306c9b92931
-- title:
--   §4.5 and Appendix B — complementary global-job rounding: E[A_glob] ≥ G − 5ηF
-- statement:
--   Fix configuration distributions $x_{B,C}$ with their stored schedules (a feasible solution of the relaxation), $\eta=1/q\le1/100$, and an integer $\Delta$ with
--   $$\frac{4(\lfloor\log_2T\rfloor+1)}{\eta^4}\le\Delta\qquad\text{and}\qquad F\ge\frac{m\Delta|\mathcal B|}{\eta}.$$
--   The complementary global-job rounding of Appendix B, applied to these distributions and stored schedules, returns a feasible schedule on every outcome of positive probability, of cardinality $A_{\mathrm{glob}}$ with
--   $$\mathbb E[A_{\mathrm{glob}}]\ge G-5\eta F.$$
--
--   Taking the largest of this schedule and the two outputs of Algorithm 1 gives the $21/17+\varepsilon$ ratio in pseudopolynomial time.
--
--   **Formalization Note** Jobs and blocks have finite index types; expectations are finite weighted sums over the explicitly defined sampling outcomes.
--
--   Differences from the source:
--   - generalization: the logarithmic choice ∆ = 4η^{−4}(⌈log₂(T + 1)⌉ + 1) → any integer ∆ with 4(⌊log₂ T⌋ + 1)/η⁴ ≤ ∆; reason: the proof uses only this inequality (p. 30); the source’s ∆ satisfies it because ⌈log₂(T+1)⌉ = ⌊log₂ T⌋ + 1 for T ≥ 1
--   - generalization: "place them in any order", ties in deadline or release order → feasibility for every injective ordering key; reason: covers every choice the procedure leaves free
--   - reading: "returns a feasible schedule" → feasible on every assignment outcome of positive probability; reason: zero-probability assignments (e.g. to blocks where the job cannot run) are never produced
--   - generalization: the residual instance after discarding individually infeasible jobs in §2, with positive machine count and configuration cap → also permits jobs with processing time exceeding their window length, zero machines, a zero configuration cap; reason: individually infeasible jobs occur in no feasible configuration or schedule; the extra zero cases have only empty configurations or zero marginals, and every source instance is included
-- source:
--   Tong and Xu, Coordinating Boundaries: Improved Approximation Algorithms for Unweighted Non-Preemptive Throughput Maximization, preprint of October 25, 2026 (STOC 2027 submission #141; source.pdf sha256 59f76539a5ee555f9e56603a067e9f858f38d003011e90b1716085348673687e), p. 26, §4.5 (statement); pp. 29–31, Appendix B (procedure and proof)

import Mathlib
import Definitions.Def_CoordBoundaries_Throughput_GlobalRounding

open Classical

namespace CoordBoundaries.Throughput

/-- **§4.5 and Appendix B** (Tong–Xu, p. 26; proof pp. 29–31): complementary global-job rounding.
Fix configuration distributions `x_{B,C}` with stored schedules, `η = 1/q ≤ 1/100`, and an integer
`∆` with `4(⌊log₂ T⌋ + 1)/η⁴ ≤ ∆` and `F ≥ m∆|ℬ|/η`. The rounding returns a feasible schedule on every
outcome of positive probability (for every choice of the orders left free by the placement rule),
of cardinality `A_glob` with `E[A_glob] ≥ G − 5ηF`. -/
theorem global_job_rounding {I : Instance} (hI : I.Valid) {P : Partition I.T} {K Δ q : ℕ}
    (hq : 100 ≤ q) (s : ConfigSol I P K)
    (hΔ : 4 * ((Nat.log 2 I.T : ℝ) + 1) / eta q ^ 4 ≤ Δ) (hD₁ : s.DenseBlocks Δ q) :
    (∀ key : Fin I.n → ℕ, Function.Injective key →
      ∀ α : Assign I P, s.asgLaw q α ≠ 0 → Feasible I (P.globSched q key α)) ∧
    s.G - 5 * eta q * s.F ≤ ∑ α : Assign I P, s.asgLaw q α * (P.Aglob q α : ℝ) := by sorry

end CoordBoundaries.Throughput

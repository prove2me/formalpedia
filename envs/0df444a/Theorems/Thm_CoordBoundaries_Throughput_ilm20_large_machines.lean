-- Prove2me | Theorems.Thm_CoordBoundaries_Throughput_ilm20_large_machines
-- name    : CoordBoundaries.Throughput.ilm20_large_machines
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:35:09.763301+00:00
-- url     : https://prove2.me/theorems/dac0069b-8d71-4250-871e-89e47a4f1c03
-- title:
--   Proof of Theorem 1.1, p. 27 — [ILM20, Theorem 1.2]: expected fraction 1 − O(√(log m/m)) − δ for many machines
-- statement:
--   For every fixed $\delta>0$, the algorithm of [ILM20, Theorem 1.2] runs in polynomial time with arbitrary binary time data and retains expected fraction
--   $$1-O\big(\sqrt{\log m/m}\big)-\delta$$
--   of the optimum for unweighted jobs. Formally: there are constants $C>0$ and $m_0$ such that for every $\delta>0$ some randomized polynomial-time algorithm, on every instance with $m\ge m_0$ machines, always returns a feasible schedule and has expected throughput at least $\big(1-C\sqrt{\ln m/m}-\delta\big)\mathrm{OPT}$.
--
--   The proof of Theorem 1.1 uses it to remove the assumption that the number of machines is fixed. This paper gives no proof; the result is Im, Li and Moseley, SIAM J. Discrete Math. 34(3):1649–1669, 2020.
--
--   **Formalization Note** The retained-fraction predicate uses the published RAM, with a feasible output and a cost bound on every coin string.
--
--   Differences from the source:
--   - reading: O(√(log m/m)) → C·√(ln m/m) for all m ≥ m₀, with C and m₀ chosen before δ; reason: O(·) is asymptotic in m; read at every m ≥ 1 it would assert a one-machine PTAS, which p. 7 calls open
--   - reading: "runs in polynomial time" → cost at most N^k on every coin string, k chosen after δ; reason: polynomial in the input length for each fixed δ
--   - reading: an algorithm for the problem → its output is a feasible schedule on every coin string; reason: the proof of Theorem 1.1 needs feasible outputs
--   - encoding: "polynomial time" / "pseudopolynomial time" for an algorithm → one program of the published unit-cost integer RAM `CongruencyTU` and a bit-length polynomial, fixed before the input; every run halts within the stated cost and keeps every register within q(input bit size) bits; reason: unit-cost arithmetic on polynomially many bits equals bit cost up to polynomial factors
-- source:
--   Tong and Xu, Coordinating Boundaries: Improved Approximation Algorithms for Unweighted Non-Preemptive Throughput Maximization, preprint of October 25, 2026 (STOC 2027 submission #141; source.pdf sha256 59f76539a5ee555f9e56603a067e9f858f38d003011e90b1716085348673687e), p. 27, proof of Theorem 1.1 (citing [ILM20, Theorem 1.2])

import Mathlib
import Definitions.Def_CoordBoundaries_Throughput_Problem

open Classical

namespace CoordBoundaries.Throughput

/-- **[ILM20, Theorem 1.2] as used in the proof of Theorem 1.1** (Tong–Xu, p. 27). There are
constants `C > 0` and `m₀` such that for every fixed `δ > 0` a randomized polynomial-time algorithm,
on every instance with arbitrary binary time data and `m ≥ m₀` machines, always returns a feasible
schedule and retains expected fraction `1 − C√(log m / m) − δ` of the optimum. -/
theorem ilm20_large_machines :
    ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ δ : ℝ, 0 < δ → ∃ k : ℕ,
      RetainsWithin (fun I => 1 - C * Real.sqrt (Real.log I.m / I.m) - δ)
        (fun I => m₀ ≤ I.m) (fun I => N I ^ k) := by sorry

end CoordBoundaries.Throughput

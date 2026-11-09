-- Prove2me | Theorems.Thm_CoordBoundaries_Throughput_theorem_1_1
-- name    : CoordBoundaries.Throughput.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:35:16.196178+00:00
-- url     : https://prove2.me/theorems/17b4500d-aa49-4491-9e51-108fda1c455b
-- title:
--   Theorem 1.1 — expected ratios 17/13 + ε in polynomial time and 21/17 + ε in pseudopolynomial time
-- statement:
--   For every fixed $\varepsilon>0$, unweighted nonpreemptive throughput maximization on any number of identical machines admits randomized algorithms with expected approximation ratios $17/13+\varepsilon$ in polynomial time and $21/17+\varepsilon$ in pseudopolynomial time. Every returned schedule is feasible. The respective running times are
--   $$n^{O_\varepsilon(1)}\,\mathrm{poly}(N)\qquad\text{and}\qquad (nT)^{O_\varepsilon(1)}\,\mathrm{poly}(N).$$
--   Here $n$ is the number of jobs, $T=\max_jd_j$ the time horizon, $N$ the input length, and an expected $\rho$-approximation always returns a feasible schedule and has expected throughput at least $\mathrm{OPT}/\rho$, where $\mathrm{OPT}$ is the maximum throughput.
--
--   Formally: there is a polynomial $p$ such that for every $\varepsilon>0$ there are exponents $c,c'$ and two programs which, on every instance and every string of random bits, halt within $\max(1,n)^c p(N)$, respectively $\max(1,nT)^{c'}p(N)$, steps with a feasible schedule, and whose expected throughput is at least $\mathrm{OPT}/(17/13+\varepsilon)$, respectively $\mathrm{OPT}/(21/17+\varepsilon)$.
--
--   This improves the $4/3+\varepsilon$ and $5/4+\varepsilon$ guarantees of Armbruster, Grandoni, Tinguely and Wiese (STOC 2026).
--
--   **Formalization Note** OPT uses real start times; the RAM output uses integer starts, and both budgets hold on every coin string.
--
--   Differences from the source:
--   - reading: running times n^{O_ε(1)} poly(N) and (nT)^{O_ε(1)} poly(N) → one polynomial p chosen before ε; exponents c (and the programs) chosen after ε; budgets max(1,n)^c·p(N) and max(1,nT)^c·p(N); reason: the subscript ε is attached to the exponent only; letting poly(N) depend on ε would collapse the bound to N^{O_ε(1)}. max(1,·) only matters at n = 0
--   - encoding: randomized algorithm, expected throughput → a program reading at most B random bits; the expectation is the uniform average over the 2^B bit strings; the time bound holds for every bit string; reason: §4.5 (pp. 26–27) implements every draw with a fixed number of unbiased bits "to bound the running time for every random outcome"
--   - encoding: expected throughput at least OPT/ρ → OPT ≤ ρ · E[throughput]; reason: equivalent for ρ > 0
--   - encoding: "Every returned schedule is feasible" → on every bit string the output decodes to a feasible schedule with integer start times; reason: integer start times are no restriction (p. 8); OPT is over real start times as defined on p. 2
--   - encoding: integer time data with r_j ≥ 0 → natural numbers; reason: same instances
--   - generalization: m identical machines (m ≥ 1) → m = 0 is also allowed; reason: then OPT = 0 and the empty output qualifies; the source instances are included
--   - encoding: "polynomial time" / "pseudopolynomial time" for an algorithm → one program of the published unit-cost integer RAM `CongruencyTU` and a bit-length polynomial, fixed before the input; every run halts within the stated cost and keeps every register within q(input bit size) bits; reason: unit-cost arithmetic on polynomially many bits equals bit cost up to polynomial factors
-- source:
--   Tong and Xu, Coordinating Boundaries: Improved Approximation Algorithms for Unweighted Non-Preemptive Throughput Maximization, preprint of October 25, 2026 (STOC 2027 submission #141; source.pdf sha256 59f76539a5ee555f9e56603a067e9f858f38d003011e90b1716085348673687e), p. 2, Theorem 1.1 (proof p. 27)

import Mathlib
import Definitions.Def_CoordBoundaries_Throughput_Problem

open Classical

namespace CoordBoundaries.Throughput

/-- **Theorem 1.1** (Tong–Xu, p. 2). For every fixed `ε > 0`, unweighted nonpreemptive throughput
maximization on any number of identical machines admits randomized algorithms with expected
approximation ratios `17/13 + ε` in polynomial time and `21/17 + ε` in pseudopolynomial time; every
returned schedule is feasible; the running times are `n^{O_ε(1)} poly(N)` and
`(nT)^{O_ε(1)} poly(N)` — read with one polynomial `p` fixed before `ε` and the exponent depending
on `ε`, worst case over the random bits. -/
theorem theorem_1_1 :
    ∃ p : Polynomial ℕ, ∀ ε : ℝ, 0 < ε →
      (∃ c : ℕ, ApproxWithin (17 / 13 + ε) (fun _ => True)
          (fun I => (max 1 I.n) ^ c * p.eval (N I))) ∧
      (∃ c : ℕ, ApproxWithin (21 / 17 + ε) (fun _ => True)
          (fun I => (max 1 (I.n * I.T)) ^ c * p.eval (N I))) := by sorry

end CoordBoundaries.Throughput

-- Prove2me | Theorems.Thm_CoordBoundaries_Throughput_pricing_problem_2
-- name    : CoordBoundaries.Throughput.pricing_problem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:44:01.744024+00:00
-- url     : https://prove2.me/theorems/968c7bac-949e-4872-b5cb-379296811e17
-- title:
--   §4.4, problem (2) — exact pricing with required jobs in time (2m)^{O(K)} poly(n, T, N, Λ)
-- statement:
--   There are an absolute constant $c$, a polynomial $p$ and a deterministic algorithm with the following property. Given an instance with $m\ge1$, a candidate partition, a block $B=[s,t)$, a cap $K$, a tracked set $H_B$ with $|H_B|\le 8K$, rational coefficients $w_j$ and a rational table $\alpha(A)$ for $A\subseteq H_B$ (either may be negative), the algorithm solves
--   $$\max_{C\in\mathcal C(B)}\Big\{\sum_{j\in C}w_j+\alpha(C\cap H_B)\Big\}\tag{2}$$
--   exactly — it outputs a configuration attaining the maximum together with a feasible witness schedule inside $B$ — in running time $(2m)^{cK}\,p(n+T+N+\Lambda)$, where $\Lambda$ is the encoding length of the supplied coefficients and table.
--
--   This exact separation oracle lets the stage LPs be solved without enumerating configurations.
--
--   **Formalization Note** The output is a list of (job, machine, integer start) triples; its job set is the configuration.
--
--   Differences from the source:
--   - generalization: a tracked set H_B ⊆ {j global : B ∈ {B_L(j), B_R(j)}} → any set of jobs with |H_B| ≤ 8K; reason: the dynamic program and the subset enumeration never use the tracked property
--   - reading: "(2m)^{O(K)} poly(n, T, N, Λ)" → an absolute c and polynomial p: cost at most (2m)^{cK}·p(n + T + N + Λ); reason: the constants are not subscripted
--   - reading: the color-coding algorithm with a perfect hash family [AYZ95] → a deterministic program; reason: the family of [AYZ95, §4] is constructed deterministically
--   - reading: m identical machines → 1 ≤ m; reason: the source assumes at least one machine; the budget (2m)^{cK} would vanish at m = 0
--   - encoding: rational coefficients and table → integer numerators with positive natural denominators, the table indexed by the subsets of H_B; reason: standard binary representation of rationals
--   - encoding: "polynomial time" / "pseudopolynomial time" for an algorithm → one program of the published unit-cost integer RAM `CongruencyTU` and a bit-length polynomial, fixed before the input; every run halts within the stated cost and keeps every register within q(input bit size) bits; reason: unit-cost arithmetic on polynomially many bits equals bit cost up to polynomial factors
--   - generalization: the residual instance after discarding individually infeasible jobs in §2, with positive machine count and configuration cap → also permits jobs with processing time exceeding their window length, a zero configuration cap; reason: individually infeasible jobs occur in no feasible configuration or schedule; the extra zero cases have only empty configurations or zero marginals, and every source instance is included
-- source:
--   Tong and Xu, Coordinating Boundaries: Improved Approximation Algorithms for Unweighted Non-Preemptive Throughput Maximization, preprint of October 25, 2026 (STOC 2027 submission #141; source.pdf sha256 59f76539a5ee555f9e56603a067e9f858f38d003011e90b1716085348673687e), pp. 24–25, §4.4, problem (2) and the running-time paragraph

import Mathlib
import Definitions.Def_CoordBoundaries_Throughput_Pricing

open Classical CongruencyTU

namespace CoordBoundaries.Throughput

/-- **§4.4, problem (2)** (Tong–Xu, pp. 24–25): exact pricing with required jobs. There are an
absolute constant `c`, a polynomial `p` and one deterministic program such that, for every valid
instance with `m ≥ 1` and every pricing input (block `B` of a candidate partition, cap `K`, tracked
set `H_B` with `|H_B| ≤ 8K`, rational weights `w_j` and table `α(A)`, possibly negative), the program
runs in time `(2m)^{c·K} · p(n + T + N + Λ)`, `Λ` the encoding length of the coefficients, and
outputs a configuration `C ∈ 𝒞(B)` attaining `max_{C ∈ 𝒞(B)} {Σ_{j ∈ C} w_j + α(C ∩ H_B)}`, together
with a feasible witness schedule of `C` inside `B`. -/
theorem pricing_problem_2 :
    ∃ (c : ℕ) (p : Polynomial ℕ) (Pg : Program) (qg : Polynomial ℕ),
      ∀ I : Instance, I.Valid → 1 ≤ I.m → ∀ X : PricingInput I, X.Valid →
        RunBounded Pg noOracle noCoins X.encode
            ((2 * I.m) ^ (c * X.K) * p.eval (I.n + I.T + N I + bitSize X.encCoeffs)) qg 0 ∧
        ∃ σ : Sched I,
          decode I (outputAfter Pg noOracle noCoins X.encode
            ((2 * I.m) ^ (c * X.K) * p.eval (I.n + I.T + N I + bitSize X.encCoeffs))) = some σ ∧
          X.P.WitnessIn X.k (scheduled σ) σ ∧
          scheduled σ ∈ X.P.configs X.K X.k ∧
          ∀ C ∈ X.P.configs X.K X.k, X.objective C ≤ X.objective (scheduled σ) := by sorry

end CoordBoundaries.Throughput

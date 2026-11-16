-- Prove2me | Theorems.Thm_FairKMeans_Supplement_theorem_7
-- name    : FairKMeans.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:03:09.710758+00:00
-- url     : https://prove2.me/theorems/e6310dc4-bc03-45bb-be11-8cb8b21af90d
-- title:
--   Theorem 7 — no polynomial-time $(3-\delta)$-approximation for fair $k$-means unless $\mathrm P=\mathrm{NP}$, even on the line
-- statement:
--   Let $\delta\in(0,1]$ be fixed. Suppose a deterministic polynomial-time algorithm (a Turing machine reading the bit encoding of the instance) returns, for every rational instance of fair $k$-means in dimension $d=1$ whose groups have $\beta_i=1/2$ and $\alpha_i\in\{1/2,1\}$ and which has a fair solution, the encoding of at most $k$ centers $S$ and an $(\alpha,\beta)$-fair fractional assignment $\phi_S$ with
--
--   $$\mathrm{Cost}(P,S,\phi_S)\le(3-\delta)\,\mathrm{OPT},$$
--
--   where $\mathrm{OPT}$ is the optimal cost of the integral version. Then $\mathrm P=\mathrm{NP}$.
--
--   Equivalently: if $\mathrm P\ne\mathrm{NP}$, no polynomial-time algorithm achieves the ratio $3-\delta$ against $\mathrm{OPT}$, even for points on a line. Since Theorem 3 achieves $3+O(\varepsilon)$ in fixed dimension, the constant $3$ is the approximation threshold of fractional fair $k$-means in fixed dimension; since every integral assignment is fractional, the bound applies to algorithms returning integral solutions as well.
--
--   Differences from the source:
--   - encoding: if P ≠ NP, then no polynomial-time algorithm returns … → if some algorithm returns … then OAI.MetricKMedian.Complexity.P = OAI.MetricKMedian.Complexity.NP; reason: the contrapositive; P and NP of the published KMedianThreshold
--   - encoding: polynomial-time algorithm (on a Turing machine, footnote 1) → alg : RatInst → List Bool with FinitePolyTime encodeRatInst id alg (Mathlib TM2 machine, finite work alphabets, polynomial time in the input length), whose output is the bit encoding of a rational solution; reason: footnote 1: Theorem 7 concerns polynomial time on a Turing machine; inputs and outputs of a Turing machine are finite strings
--   - encoding: instance of fair k-means (real data) → rational instances (points of ℚ, α, β ∈ [0,1] ∩ ℚ) with an explicit injective bit encoding, cast into the published FairKMeans.Instance 1 n m; reason: a Turing machine reads finite strings; the reduction's instances (p.46) have rational data
--   - reading: for every instance of fair k-means … This remains true even for instances with d = 1, β_i = 1/2 and α_i ∈ {1/2, 1} → correctness demanded only on restricted instances in d = 1; reason: the theorem's strongest stated form; an algorithm correct on every instance is correct on these
--   - reading: for every instance → for every restricted instance that has a fair solution; reason: on an instance without a fair solution no valid output exists, so the literal reading makes the theorem vacuous; the reduction (p.46) produces only instances with a fair solution
--   - encoding: at most k centers S ⊂ ℝ and a fair fractional assignment → a rational solution: s ≤ k centers on the line (an indexed family, duplicates allowed) and an n × s rational matrix, cast to ℝ; published IsAssignment, IsFair, cost, OPT; reason: outputs of a Turing machine are finite strings; duplicate centers change no cost or fairness
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Theorem 7, p.5 (PDF p.7) with footnote 1 (PDF p.7); proof, Section 7, pp.38–46 (PDF pp.40–48)

import Mathlib
import Definitions.Def_FairKMeans_Model
import Definitions.Def_KMedianThreshold
import Definitions.Def_FairKMeans_Supplement_Hardness

namespace FairKMeans.Supplement

open FairKMeans

/-- **Theorem 7 (Hardness of approximation)**, p.5 (PDF 7); proof in Section 7, pp.38–46
(PDF 40–48). Cheng–Mo–Song–Ding, arXiv:2609.07974 (held version, sha256 73e9312c…).

Let `δ ∈ (0, 1]` be fixed. If some deterministic polynomial-time algorithm (a Turing machine with
finite work alphabets, `FinitePolyTime` of `KMedianThreshold`, reading the bit encoding of the
instance) returns, for every rational instance of fair k-means with `d = 1`, `β_i = 1/2` and
`α_i ∈ {1/2, 1}` that has a fair solution, the encoding of at most `k` centers `S` and an
`(α, β)`-fair fractional assignment `φ_S` with `Cost(P, S, φ_S) ≤ (3 − δ) OPT`, then `P = NP`.

**Formalization Note.** The contrapositive of "if `P ≠ NP`, no polynomial-time algorithm …".
Correctness is demanded only on the restricted class ("this remains true even for instances with
`d = 1` and groups with `β_i = 1/2` and `α_i ∈ {1/2, 1}`"), which is the strongest form: an
algorithm for all instances is in particular one for these. It is demanded only on instances with
a fair solution: on the others no valid output exists, and the reduction (p.46) produces only
instances with a fair solution. Footnote 1: Theorem 7 concerns polynomial time on a Turing
machine. -/
theorem theorem_7 (δ : ℝ) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (alg : RatInst → List Bool)
    (hpoly : OAI.MetricKMedian.Complexity.FinitePolyTime encodeRatInst id alg)
    (hcorrect : ∀ J : RatInst, J.Restricted → HasFairSolution J.toInstance →
      ∃ sol : RatSol J.n, alg J = encodeRatSol sol ∧ Valid δ J sol) :
    OAI.MetricKMedian.Complexity.P = OAI.MetricKMedian.Complexity.NP := by sorry

end FairKMeans.Supplement

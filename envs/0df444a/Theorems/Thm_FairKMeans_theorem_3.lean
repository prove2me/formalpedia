-- Prove2me | Theorems.Thm_FairKMeans_theorem_3
-- name    : FairKMeans.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:34:27.019347+00:00
-- url     : https://prove2.me/theorems/ea90ec0f-e7d2-463b-b537-474112e48f41
-- title:
--   Theorem 3 — exactly fair $(2\rho+1+\epsilon)$-approximation for fractional fair $k$-means with one $k$-means call and $O((\rho/\epsilon)^2)$ LPs
-- statement:
--   Let $\rho\ge1$, $\varepsilon\in(0,1]$ and $\eta=\min\{1/10,\varepsilon/(3\rho)\}$. There is a constant $c$, depending only on $\rho$ and $\varepsilon$, such that the following holds for every dimension $d$, every instance $(P,P^{(1)},\dots,P^{(m)},k,\alpha,\beta)$ with a fair solution, every exact fair-LP oracle, every exact LP (29) oracle and every $\rho$-approximate weighted $k$-means oracle. Algorithm 1, run with these,
--
--   1. stops by its own test;
--   2. returns at most $k$ centers $S$ and a fractional assignment $\phi_S$ that satisfies all $(\alpha,\beta)$-fairness constraints exactly, with
--
--   $$\mathrm{Cost}(P,S,\phi_S)\le(2\rho+1+\varepsilon)\,\mathrm{OPT}_{\mathrm{frac}}\le(2\rho+1+\varepsilon)\,\mathrm{OPT}; \tag{1}$$
--
--   3. calls the $k$-means oracle exactly once and solves at most $\lceil576/\eta^2\rceil+3\le57604(\rho/\varepsilon)^2$ linear programs;
--   4. every linear program it solves (variables plus constraints), the input of the $k$-means call, and the number of real-RAM arithmetic operations outside the oracles are at most $c\,(n+d+m+k+2)^c$.
--
--   This improves the ratio $1+4\rho$ of Song, Mo and Ding; in fixed dimension, with a PTAS for weighted $k$-means, the ratio is $3+O(\varepsilon)$.
--
--   Differences from the source:
--   - encoding: a deterministic polynomial-time algorithm with access to a ρ-approximation algorithm → Algorithm 1 as a Lean function of an LP oracle pair and a k-means oracle, in the cost model of footnote 1; reason: real-RAM arithmetic counted, LP and k-means time counted separately as in Proposition 29; deterministic as a function of its oracles
--   - reading: a … algorithm computes → Algorithm 1 itself, for every pair of exact LP oracles and every ρ-approximate k-means oracle; reason: the paper's witness; stronger than an existential
--   - encoding: WCS_δ (part 1 of Lemma 15 in fixed dimension, part 2 otherwise) → Lemma 15 part 2 in every dimension; reason: p.20: part 2 alone suffices for polynomial time
--   - reading: O((ρ/ϵ)²) linear programs → ⌈576/η²⌉ + 3 ≤ 57604(ρ/ϵ)²; reason: Proposition 29 with 1/η ≤ 10ρ/ϵ
--   - reading: each of size polynomial in the input (for fixed ϵ and ρ, p.25) → ∃ c depending only on (ρ, ϵ), bound c·(n+d+m+k+2)^c uniformly in d and the instance; reason: k enters through the final LP's n·|S_π| ≤ nk variables, which the paper bounds by k ≤ n (p.36), never assumed
--   - encoding: standing assumption: the instance has a fair solution (p.19) → hypothesis HasFairSolution; reason: stated once for the whole analysis
--   - encoding: center sets S ⊂ ℝ^d, k-means outputs → indexed families (duplicates allowed), nonempty k-means outputs; reason: merging duplicate centers changes no cost or fairness; the empty set has infinite cost
--   - encoding: π(t) of a zero column (undefined) → Lean's 0⁻¹ • 0 = 0, always multiplied by the weight 0; reason: Lean convention; no sum changes
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Theorem 3, p.3 (PDF p.5); footnote 1, p.5 (PDF p.7); proof in Section 6.5, pp.34–35 (PDF pp.36–37)

import Mathlib
import Definitions.Def_FairKMeans_Model
import Definitions.Def_FairKMeans_WeightedKMeans
import Definitions.Def_FairKMeans_RelaxedSolution
import Definitions.Def_FairKMeans_CandidateSets
import Definitions.Def_FairKMeans_LPOracles
import Definitions.Def_FairKMeans_Algorithm1

namespace FairKMeans

/-- **Theorem 3 (Fractional fair k-means)**, p.3 (PDF 5). Cheng–Mo–Song–Ding,
arXiv:2609.07974 (held version, sha256 73e9312c…).

Let `ρ ≥ 1` and `ε ∈ (0,1]`, and `η = min{1/10, ε/(3ρ)}`. There is `c` (depending only on `ρ`
and `ε`) such that for every dimension `d`, every instance with a fair solution (p.19), every
exact fair-LP oracle, every exact LP (29) oracle and every ρ-approximate weighted k-means oracle,
Algorithm 1 (p.25) stops by its own test, returns at most `k` centers `S` and an exactly
`(α, β)`-fair fractional assignment `φ_S` with
`Cost(P, S, φ_S) ≤ (2ρ+1+ε) OPT_frac ≤ (2ρ+1+ε) OPT` (1), calls the k-means oracle exactly once,
solves at most `⌈576/η²⌉ + 3 ≤ 57604 (ρ/ε)²` linear programs, and every LP (variables plus
constraints), the k-means input and the number of real-RAM operations outside the oracles are at
most `c (n+d+m+k+2)^c`.

**Formalization Note.** "A deterministic polynomial-time algorithm … with access to a
ρ-approximation algorithm" is Algorithm 1 as a function of its oracles, in the cost model of
footnote 1 (real-RAM arithmetic counted, LP and k-means time separate). -/
theorem theorem_3 (ρ ε : ℝ) (hρ : 1 ≤ ρ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ c : ℕ, ∀ (d n m : ℕ) (I : Instance d n m), HasFairSolution I →
      ∀ (fairLP : FairLPOracle d n) (lp29 : LP29Oracle d n) (KM : KMOracle d),
        IsFairLPOracle I fairLP → IsLP29Oracle I lp29 → IsRhoApprox ρ I.k KM →
        (alg1 ρ ε I fairLP lp29 KM).stopped ∧
        (alg1 ρ ε I fairLP lp29 KM).s ≤ I.k ∧
        IsAssignment (alg1 ρ ε I fairLP lp29 KM).assign ∧
        IsFair I (alg1 ρ ε I fairLP lp29 KM).assign ∧
        cost I (alg1 ρ ε I fairLP lp29 KM).centers (alg1 ρ ε I fairLP lp29 KM).assign ≤
          (2 * ρ + 1 + ε) * OPTfrac I ∧
        (2 * ρ + 1 + ε) * OPTfrac I ≤ (2 * ρ + 1 + ε) * OPT I ∧
        (alg1 ρ ε I fairLP lp29 KM).kmCalls = 1 ∧
        (alg1 ρ ε I fairLP lp29 KM).lpCalls ≤ ⌈576 / eta ρ ε ^ 2⌉₊ + 3 ∧
        ((alg1 ρ ε I fairLP lp29 KM).lpCalls : ℝ) ≤ 57604 * (ρ / ε) ^ 2 ∧
        (∀ L ∈ (alg1 ρ ε I fairLP lp29 KM).lpSizes, L.1 + L.2 ≤ c * (n + d + m + I.k + 2) ^ c) ∧
        (alg1 ρ ε I fairLP lp29 KM).kmInputSize ≤ c * (n + d + m + I.k + 2) ^ c ∧
        (alg1 ρ ε I fairLP lp29 KM).arithOps ≤ c * (n + d + m + I.k + 2) ^ c := by sorry

end FairKMeans

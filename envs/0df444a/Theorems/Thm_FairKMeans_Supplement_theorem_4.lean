-- Prove2me | Theorems.Thm_FairKMeans_Supplement_theorem_4
-- name    : FairKMeans.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:02:33.924014+00:00
-- url     : https://prove2.me/theorems/1da34df7-2858-497c-9c67-a6073eb0f513
-- title:
--   Theorem 4 — $k$-sparse Wasserstein barycenters: a $(2\rho+1+\epsilon)$-approximation with one $k$-means call
-- statement:
--   Let $\rho\ge1$ and $\varepsilon\in(0,1]$. There is a constant $c$, depending only on $\rho$ and $\varepsilon$, such that the following holds for every dimension $d$, every family of $m\ge1$ discrete probability distributions $P^{(1)},\dots,P^{(m)}$ on $\mathbb R^d$ with $n$ atoms in total, every $k\ge1$, every pair of exact LP oracles for the associated instance and every $\rho$-approximate weighted $k$-means oracle. The algorithm of the proof (the weighted Algorithm 1 on the associated instance, followed by the masses $w(s)/m$) returns a probability distribution $B$ supported on at most $k$ points with
--
--   $$\mathrm{Cost}_{WB}(B)\le(2\rho+1+\varepsilon)\,\mathrm{OPT}_{WB};$$
--
--   it makes at most $c$ calls to the $k$-means oracle and solves at most $c$ linear programs, and every linear program (variables plus constraints), the input of the $k$-means call and the number of real-RAM operations outside the oracles are at most $c\,(n+d+m+k+2)^c$.
--
--   In fixed dimension, the PTAS for weighted $k$-means gives the ratio $3+O(\varepsilon)$, improving the previous ratios $(2+\sqrt\rho)^2$ and $1+4\rho$ for $k$-sparse barycenters.
--
--   Differences from the source:
--   - encoding: a deterministic polynomial-time algorithm with access to a ρ-approximation algorithm for weighted k-means → the algorithm of the proof (baryAlg: weighted Algorithm 1 on the associated instance, then masses w(s)/m) as a Lean function of two exact LP oracles and a k-means oracle, in the cost model of footnote 1; reason: real-RAM arithmetic counted and LP and k-means time counted separately, as in the published Theorem 3; deterministic as a function of its oracles
--   - reading: a … algorithm computes → this algorithm, for every exact LP oracle pair and every ρ-approximate k-means oracle; reason: the paper's witness (proof, p.48); stronger than an existential
--   - reading: polynomial-time → ∃ c depending only on (ρ, ϵ): at most c k-means and c LP calls, and every LP (variables plus constraints), the k-means input and the operation count at most c·(n+d+m+k+2)^c; reason: the reading of the published Theorem 3, for fixed ρ and ϵ, uniformly in d and the instance
--   - encoding: discrete probability distributions P(1), …, P(m) with n atoms in total → n indexed atoms with owner q ∈ [m], masses > 0 summing to 1 per distribution, and m ≥ 1; reason: the notation of Section 8 (p.47); m ≥ 1 is implicit in 1/m
--   - encoding: probability distribution B supported on at most k points (masses b_s > 0) → a family of s ≤ k atoms with masses ≥ 0 summing to 1 (zero masses and repeated atoms allowed); reason: a zero-mass atom receives no mass and plans to repeated atoms merge, so W2, CostWB and OPTWB are unchanged; the support of the output has at most s ≤ k points
--   - encoding: W2(P(i), B), the minimum over transport plans → sInf over plans (51); reason: for a probability distribution the plans form a nonempty compact polytope, so the infimum is attained
--   - encoding: the weighted version of Algorithm 1 run on the associated fair instance (Remark 44) → alg1H on assoc I, whose constraints are those of Remark 31 for α_i = β_i = 1/m; reason: Remark 31: the same feasible assignment matrices as the fairness constraints (12)
--   - encoding: WCS_δ (part 1 of Lemma 15 in fixed dimension, part 2 otherwise) → Lemma 15 part 2 in every dimension; reason: p.20: part 2 alone suffices for polynomial time; as in the published Theorem 3
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Theorem 4, p.3 (PDF p.5); footnote 1, p.5 (PDF p.7); proof, Section 8, pp.47–48 (PDF pp.49–50)

import Mathlib
import Definitions.Def_FairKMeans_Model
import Definitions.Def_FairKMeans_WeightedKMeans
import Definitions.Def_FairKMeans_LPOracles
import Definitions.Def_FairKMeans_Algorithm1
import Definitions.Def_FairKMeans_Supplement_Constrained
import Definitions.Def_FairKMeans_Supplement_ConstrainedLP
import Definitions.Def_FairKMeans_Supplement_ConstrainedAlgorithm
import Definitions.Def_FairKMeans_Supplement_Barycenter

namespace FairKMeans.Supplement

open FairKMeans

/-- **Theorem 4 (k-sparse Wasserstein barycenters)**, p.3 (PDF 5); proof p.48 (PDF 50).
Cheng–Mo–Song–Ding, arXiv:2609.07974 (held version, sha256 73e9312c…).

Let `ρ ≥ 1` and `ε ∈ (0, 1]`. There is `c` (depending only on `ρ` and `ε`) such that for every
dimension `d`, every family of `m ≥ 1` discrete probability distributions on `ℝ^d` with `n` atoms
in total and every `k ≥ 1`, and all oracles meeting their specifications on the associated
instance (an exact feasible-assignment-LP oracle, an exact LP (29) oracle, a ρ-approximate
weighted k-means oracle), the algorithm of the proof (weighted Algorithm 1 on the associated
instance, then the masses `w(s)/m`) returns a probability distribution `B` supported on at most
`k` points with `CostWB(B) ≤ (2ρ+1+ε) OPTWB`, making at most `c` k-means calls and `c` LP calls,
and every LP, the k-means input and the number of operations outside the oracles are at most
`c (n+d+m+k+2)^c`.

**Formalization Note.** "A deterministic polynomial-time algorithm … with access to a
ρ-approximation algorithm" is read in the cost model of footnote 1 (p.5), as in the published
Theorem 3: an explicit function of its oracles with real-RAM operations counted. -/
theorem theorem_4 (ρ ε : ℝ) (hρ : 1 ≤ ρ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ c : ℕ, ∀ (d n m : ℕ) (I : BaryInstance d n m)
      (hLP : FairLPOracle d n) (lp29 : LP29Oracle d n) (KM : KMOracle d),
      IsHLPOracle (assoc I) hLP → IsHLP29Oracle (assoc I) lp29 → IsRhoApprox ρ I.k KM →
      (baryAlg ρ ε I hLP lp29 KM).dist.s ≤ I.k ∧
      (baryAlg ρ ε I hLP lp29 KM).dist.IsProb ∧
      CostWB I (baryAlg ρ ε I hLP lp29 KM).dist ≤ (2 * ρ + 1 + ε) * OPTWB I ∧
      (baryAlg ρ ε I hLP lp29 KM).run.kmCalls ≤ c ∧
      (baryAlg ρ ε I hLP lp29 KM).run.lpCalls ≤ c ∧
      (∀ L ∈ (baryAlg ρ ε I hLP lp29 KM).run.lpSizes,
        L.1 + L.2 ≤ c * (n + d + m + I.k + 2) ^ c) ∧
      (baryAlg ρ ε I hLP lp29 KM).run.kmInputSize ≤ c * (n + d + m + I.k + 2) ^ c ∧
      (baryAlg ρ ε I hLP lp29 KM).arithOps ≤ c * (n + d + m + I.k + 2) ^ c := by sorry

end FairKMeans.Supplement

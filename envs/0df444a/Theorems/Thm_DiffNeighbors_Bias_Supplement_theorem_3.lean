-- Prove2me | Theorems.Thm_DiffNeighbors_Bias_Supplement_theorem_3
-- name    : DiffNeighbors.Bias.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:15:18.191118+00:00
-- url     : https://prove2.me/theorems/b6d26cdf-dda8-4bd3-914f-16e2185e9d5d
-- title:
--   Theorem 3 (corrected: nonnegative L) — cluster DN bias with the explicit constant from Appendix A.2
-- statement:
--   Let $I$ be a finite unit set, $G$ an undirected graph without self-loops, and $f_i:\{0,1\}^I\to\mathbb R$ the potential outcomes. Write $f_i^a(z)=f_i(z^{z_i=a})$ and let $\mathcal N_i$ denote its neighbours. Suppose $\delta>0$ and $f_i^a(z)=g_i^a(\delta z)$, with $g_i^a$ twice differentiable within $[0,\delta]^I$ and all mixed second derivatives for distinct neighbours bounded in absolute value by $L$ (Assumption 2).
--
--   Assume also $L\ge0$ and neighborhood interference: $f_i(z)$ depends only on $z_i$ and its neighbours' treatments. Let $c:I\to K$ encode a partition, with each cluster independently treated with probability $p\in(0,1)$ and all units inheriting their cluster's treatment. Put $d_i=|\mathcal N_i|$, $d_i^C=|\{j\in\mathcal N_i:c(j)=c(i)\}|$, and $\mathcal N_i^C=\{c(j):j\in\mathcal N_i\}\setminus\{c(i)\}$. For the estimator (9) with this external-cluster convention, and the unchanged $\mathrm{ATE}=N^{-1}\sum_i(f_i(\vec1)-f_i(\vec0))$,
--   $$\left|\mathrm{ATE}-\mathbb E[\widehat{\mathrm{ATE}}_{\mathrm{DN-Cluster}}]\right|\le\frac1N\sum_i(d_i-d_i^C)^2L\delta^2.$$
--   The expectation is over cluster assignments. This companion theorem uses the number of neighbours outside each unit's own cluster and preserves every finite partition. The empty-population extension gives zero on both sides. Nonnegative $L$ repairs the vacuous derivative-bound corner; no positive degree or strictly positive $L$ is required.
--
--   Differences from the source:
--   - reading: Theorem 3 gives O((Σ_i(d_i-d_i^C)²/N)δ²) → bias is at most (1/N)Σ_i(d_i-d_i^C)²Lδ²; reason: the explicit Hessian bound on p. 29 has constant L; the corrected Taylor factor 1/2 in each treatment arm gives this bound for their difference
--   - reading: p. 13 names clusters containing neighbours without an explicit own-cluster exclusion → N_i^C excludes c(i); reason: p. 28 explicitly adopts this convention and p. 29 uses it; including the own cluster fails for constant outcomes, as retained in DISPROOF.md
--   - correction: the explicit proof bound uses L without restricting it when Assumption 2 is vacuous → L is explicitly nonnegative; reason: two units with one edge, singleton clusters, f=g=0, δ=1 and L=-1 meet every printed smoothness condition, but the explicit bound would be 0≤-1; only negative L in the vacuous maximum-degree-at-most-one regime is excluded
--   - reading: scaled functions and second derivatives on the box in §2.2 and Assumption 2 → functions on all unit coordinates, parameterized at δz, twice differentiable within [0,δ]^I with bounded mixed within-derivatives only for distinct neighbours; reason: neighbour functions compose with the projection; p. 6 specifies the box and presupposes these derivatives exist, with no global regularity requirement
--   - encoding: a finite partition, independent cluster Bernoulli(p) treatments, and d_i-d_i^C → a map c:I→K, finite Bernoulli expectation on K, 0<p<1, and the cardinality of neighbours outside c(i); reason: nonempty fibres recover every partition; unused labels and empty populations are harmless, propensity weights require nonzero p and 1-p, and the cardinality equals the degree difference
-- source:
--   Peng, Ye, Zheng, Differences-in-Neighbors for Network Interference in Experiments, arXiv:2503.02271v1, p. 13, Theorem 3 and (9); pp. 28–29, Appendix A.2; pp. 5–6, Assumptions 1–2

import Mathlib
import Definitions.Def_DiffNeighbors_Bias_Supplement_SmoothModel
import Definitions.Def_DiffNeighbors_Bias_Supplement_ClusterModel

namespace DiffNeighbors.Bias.Supplement

/-- Theorem 3, p. 13; Appendix A.2, pp. 28-29 supplies the explicit constant L.
Cluster assignments, not unit assignments, are independent Bernoulli(p).
The own cluster is excluded as stipulated on p. 28. Nonnegative L is explicit:
without it a degree-one graph has a vacuous Assumption 2 and negative RHS. -/
theorem theorem_3 {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (G : SimpleGraph ι) [DecidableRel G.Adj] (c : ι → κ)
    (f : ι → (ι → Bool) → ℝ) (g : ι → Bool → (ι → ℝ) → ℝ)
    (p δ L : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hδ : 0 < δ) (hL : 0 ≤ L)
    (hNI : NeighborhoodInterference G f) (hg : SmoothInterference G f g δ L) :
    |ate f - bernExp p (dnCluster G c p f)| ≤
      (Fintype.card ι : ℝ)⁻¹ *
        ∑ i, (outsideDegree G c i : ℝ) ^ 2 * L * δ ^ 2 := by sorry

end DiffNeighbors.Bias.Supplement

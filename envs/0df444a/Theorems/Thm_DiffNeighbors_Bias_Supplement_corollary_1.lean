-- Prove2me | Theorems.Thm_DiffNeighbors_Bias_Supplement_corollary_1
-- name    : DiffNeighbors.Bias.Supplement.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:15:50.293451+00:00
-- url     : https://prove2.me/theorems/e8f7c9fb-4647-4058-98fe-81ecada29c05
-- title:
--   Corollary 1, p. 9 (corrected: nonnegative L) — under Assumption 2 the DN estimator has bias at most d²δ²L
-- statement:
--   Let $I$ be a finite unit set with $N=|I|$, $G$ an undirected graph without self-loops, $\mathcal N_i$ the neighbours of $i$ and $d=\max_i|\mathcal N_i|$ the maximum degree. Let $f_i:\{0,1\}^I\to\mathbb R$ be the potential outcomes, satisfying neighborhood interference (Assumption 1): $f_i(z)$ depends only on $z_i$ and $(z_j)_{j\in\mathcal N_i}$. Write $f_i^a(z)=f_i(z^{z_i=a})$. Suppose $\delta>0$, $L\ge0$ and $f_i^a(z)=g_i^a(\delta z)$, with $g_i^a$ twice differentiable within $[0,\delta]^I$ and all mixed second derivatives for distinct neighbours bounded in absolute value by $L$ (Assumption 2).
--
--   Treat units independently with probability $p\in(0,1)$ and let $\widehat{\mathrm{ATE}}_{\mathrm{DN}}$ be the DN estimator (3), with $\mathrm{ATE}=N^{-1}\sum_i(f_i(\vec1)-f_i(\vec0))$. Then
--   $$\left|\mathrm{ATE}-\mathbb E[\widehat{\mathrm{ATE}}_{\mathrm{DN}}]\right|\le d^2\delta^2L.$$
--   This is the specialization of Theorem 1 to the smooth outcome models of §2.2: it expresses the bias in terms of the interference strength $\delta$.
--
--   Differences from the source:
--   - correction: Assumption 2 bounds an absolute value by L without stating L ≥ 0 → L is explicitly nonnegative; reason: two units with one edge, f=g=0, δ=1, L=-1 meet every printed assumption (the derivative bound over distinct neighbours is vacuous at degree one), the bias is 0 but d²δ²L=-1; only negative L in the vacuous maximum-degree-at-most-one regime is excluded
--   - reading: scaled functions and second derivatives on the box in §2.2 and Assumption 2 → functions on all unit coordinates, parameterized at δz, twice differentiable within [0,δ]^I with bounded mixed within-derivatives only for distinct neighbours; reason: neighbour functions compose with the projection; p. 6 specifies the box and presupposes these derivatives exist, with no global regularity requirement
--   - encoding: units [N], binary treatments, i.i.d. Bernoulli(p) design → a finite type, Bool-valued vectors, the published finite Bernoulli expectation and 0<p<1; reason: Bool encodes zero and one, the propensity weights require nonzero p and 1-p, and all finite source instances are retained
-- source:
--   Peng, Ye, Zheng, Differences-in-Neighbors for Network Interference in Experiments, arXiv:2503.02271v1, p. 9, Corollary 1; pp. 5–6, Assumptions 1–2; p. 7, (3)

import Mathlib
import Definitions.Def_DiffNeighbors_Bias_Supplement_SmoothModel

namespace DiffNeighbors.Bias.Supplement

/-- Corollary 1, p. 9: under Assumption 2 (with the δ-parameterization of §2.2)
the unit-level DN estimator (3) has bias at most d²δ²L, d the maximum degree.
Assumption 1 (standing throughout the paper) and the Bernoulli(p) design are
explicit. Nonnegative L is explicit: without it a graph of maximum degree one has
a vacuous Assumption 2 and a negative right-hand side. -/
theorem corollary_1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) [DecidableRel G.Adj]
    (f : ι → (ι → Bool) → ℝ) (g : ι → Bool → (ι → ℝ) → ℝ)
    (p δ L : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hδ : 0 < δ) (hL : 0 ≤ L)
    (hNI : NeighborhoodInterference G f) (hg : SmoothInterference G f g δ L) :
    |ate f - bernExp p (dnEstimator G p f)| ≤
      (G.maxDegree : ℝ) ^ 2 * δ ^ 2 * L := by sorry

end DiffNeighbors.Bias.Supplement

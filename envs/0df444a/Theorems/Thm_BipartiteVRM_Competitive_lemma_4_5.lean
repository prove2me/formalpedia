-- Prove2me | Theorems.Thm_BipartiteVRM_Competitive_lemma_4_5
-- name    : BipartiteVRM.Competitive.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:54.794982+00:00
-- url     : https://prove2.me/theorems/e2fa82a5-6751-4b66-b69f-7b0005593b78
-- title:
--   Lemma 4.5 — integrated Case 2 charge to each optimal edge
-- statement:
--   Fix $\gamma>1$, any causal deterministic tie rule, and any TA-optimal perfect matching $M^*$. For every edge $e\in M^*$, let $q_e(t)$ be its actual Case 2 charge rate: at stable times it receives $D(e)/D_r^*(t)$ from each free request whose optimal path contains $e$ and has an arrived terminal server; at event times the rate is zero. Then
--
--   $$\int_0^\infty q_e(t)\,dt\le(\gamma+1)\left(\frac{\mathrm{OPT}}{m}+D(e)\ln m\right).$$
--
--   Here $m=|R|=|S|$; membership of $e$ in the perfect matching implies $m\ge1$. The logarithm is natural. The statement retains the $\mathrm{OPT}/m$ term, includes $m=1$, and permits $\mathrm{OPT}=0$ and $D(e)=0$. This is the per-edge waiting bound used by the full theorem.
--
--   Differences from the source:
--   - encoding: finite disjoint labeled sets R and S in any metric space → finite natural-number supports on the disjoint sum of two label types, Finset edges, and arbitrary MetricSpace X; reason: every finite labeled instance can be relabeled this way; labels give no future data and distinct items may coincide in space and time
--   - encoding: the RA, SA and AU execution with an arbitrary fixed tie rule → unbounded iteration of the explicit event transition with cached simple minimum paths and a fixed View-only selector over nonempty finite choices; reason: the local rule sees only received arrival times, distances and its history; the environment advances the real clock and reveals arrivals; termination and feasible completion are conclusions, not fields or hypotheses
--   - encoding: the path component of M_t symmetric-difference Mstar containing a free request → the ordered walk which follows an Mstar edge forward and an M_t edge backward, with an analysis bound of size plus one iterations; reason: optimal_path_component concludes that this computes the whole component; the terminal server need not have arrived
--   - encoding: nonnegative waiting charges integrated from zero to infinity → the ENNReal Lebesgue integrals of the actual nonnegative rates on the nonnegative real half-line; reason: extended nonnegative integration has no nonintegrable-equals-zero default; charging_identities separately concludes integrability and the exact waiting identities
--   - encoding: the minimum actual distance-plus-both-sides-delay objective OPT in (2.1) → the real projection of its ENNReal infimum over every perfect matching and feasible real match-time function; reason: offline_attainment and the main goal conclude finiteness and attainment, so the projection never substitutes a default for an infinite value
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), p. 12, Lemma 4.5, equations (4.5)–(4.7)

import Definitions.Def_BipartiteVRM_Competitive_Specifications

set_option autoImplicit false

namespace BipartiteVRM.Competitive

/-- Lemma 4.5, p. 12: retains OPT/m, natural log, zero-length edges, and OPT=0. -/
theorem lemma_4_5 {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (hγ : 1 < γ) (tie : TieRule) (Mstar : Matching)
    (hMstar : IsOptimal I Mstar) (e : Edge) (he : e ∈ Mstar) :
    edgeCharge I γ tie Mstar e ≤
      ENNReal.ofReal ((γ + 1) * (OPT I / (I.size : ℝ) +
        edgeDistance I e * Real.log (I.size : ℝ))) := by sorry

end BipartiteVRM.Competitive

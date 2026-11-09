-- Prove2me | Theorems.Thm_CoordBoundaries_Throughput_lemma_3_3
-- name    : CoordBoundaries.Throughput.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:49:07.020136+00:00
-- url     : https://prove2.me/theorems/1f2ab1f4-0078-4890-802d-2f08e6fec6c6
-- title:
--   Lemma 3.3 — the coordinated schedule: E[A_keep] ≥ F − Z − 4P − ν − |J_miss|/2 ≥ F − 4𝒟 − ν − |J_miss|/2
-- statement:
--   Fix a configuration solution. Let $\mathcal X$ be a maximal matching of the crossing graph on good jobs, $\nu=|\mathcal X|$, and let $J_{\mathrm{miss}}$ be the excluded set. Draw the second sample from a joint law with block marginals $x_B$ under which no good job that is unmatched by $\mathcal X$ and not in $J_{\mathrm{miss}}$ is chosen at both boundary blocks, and form the coordinated schedule with a fixed tie-breaking toward the more likely boundary. Then the coordinated schedule is feasible on every outcome and
--   $$\mathbb E[A_{\mathrm{keep}}]\ge F-Z-4P-\nu-\frac{|J_{\mathrm{miss}}|}{2}\ge F-4\mathcal D-\nu-\frac{|J_{\mathrm{miss}}|}{2},$$
--   where $P=\sum_{j\text{ bad}}e_j$ and $\mathcal D=G/4-W$.
--
--   This is the guarantee of the second output of Algorithm 1; combined with Lemmas 3.2 and 3.4 it gives Theorem 3.5.
--
--   **Formalization Note** Jobs and blocks have finite index types; expectations are finite weighted sums over the explicitly defined sampling outcomes.
--
--   Differences from the source:
--   - generalization: J_miss (= ∅ for full consistency, the untracked good jobs for projected consistency) → an arbitrary finite set Jm; reason: both source cases are instances; the proof charges at most 1/2 per element whatever the set
--   - generalization: the joint sample produced by Lemma 2.2’s construction → every joint law with marginals x_B that separates the coordinated jobs; reason: the construction yields such a law and the proof uses only these two properties
--   - generalization: "breaking ties deterministically" → any rule choosing a boundary with the larger marginal; reason: the source fixes an unspecified rule; the bound holds for each
--   - generalization: a feasible solution of the consistent relaxation with the density constraints and η = 1/q → only the configuration solution (with y_j ≤ 1) is assumed; reason: the proof uses only the marginals of the joint law and y_j ≤ 1
--   - reading: "giving a feasible schedule of cardinality A_keep" (p. 19, before the lemma) → feasibility of the coordinated schedule on every outcome is a conjunct; reason: the lemma is stated about this schedule
--   - generalization: the residual instance after discarding individually infeasible jobs in §2, with positive machine count and configuration cap → also permits jobs with processing time exceeding their window length, zero machines, a zero configuration cap; reason: individually infeasible jobs occur in no feasible configuration or schedule; the extra zero cases have only empty configurations or zero marginals, and every source instance is included
-- source:
--   Tong and Xu, Coordinating Boundaries: Improved Approximation Algorithms for Unweighted Non-Preemptive Throughput Maximization, preprint of October 25, 2026 (STOC 2027 submission #141; source.pdf sha256 59f76539a5ee555f9e56603a067e9f858f38d003011e90b1716085348673687e), p. 19, Lemma 3.3 and the preceding paragraphs of §3.3

import Mathlib
import Definitions.Def_CoordBoundaries_Throughput_Rounding

open Classical

namespace CoordBoundaries.Throughput

/-- **Lemma 3.3** (Tong–Xu, p. 19). Let `𝒳` be any maximal matching of the crossing graph on good
jobs, `ν = |𝒳|`, `J_miss` the set of untracked good jobs (any finite set `Jm` here), and let the
coordinated sample be drawn from any joint law with block marginals `x_B` under which no good job
unmatched by `𝒳` and outside `Jm` appears at both boundaries. With any fixed tie-breaking toward
the more likely boundary, the coordinated schedule is feasible on every outcome and
`E[A_keep] ≥ F − Z − 4P − ν − |J_miss|/2 ≥ F − 4𝒟 − ν − |J_miss|/2`. -/
theorem lemma_3_3 {I : Instance} (hI : I.Valid) {P : Partition I.T} {K : ℕ}
    (s : ConfigSol I P K) (X : Finset (Fin I.n × Fin I.n)) (hX : s.IsMaximalCrossMatching X)
    (Jm : Finset (Fin I.n)) (side : Fin I.n → Bool) (hside : s.SideRule side)
    (μ : Tuple I P → ℝ) (hμ : IsLaw P K μ) (hmarg : s.HasMarginals μ)
    (hsep : Separates P μ (s.coordSet X Jm)) :
    (∀ ω ∈ outcomes P K, Feasible I (s.keepSched side (s.coordSet X Jm) ω)) ∧
    s.F - s.Z - 4 * s.Pbad - X.card - (Jm.card : ℝ) / 2 ≤
      ∑ ω ∈ outcomes P K, μ ω * (s.Akeep side (s.coordSet X Jm) ω : ℝ) ∧
    s.F - 4 * s.Dagg - X.card - (Jm.card : ℝ) / 2 ≤
      s.F - s.Z - 4 * s.Pbad - X.card - (Jm.card : ℝ) / 2 := by sorry

end CoordBoundaries.Throughput

-- Prove2me | Theorems.Thm_CoordBoundaries_Throughput_theorem_3_5
-- name    : CoordBoundaries.Throughput.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:49:20.410805+00:00
-- url     : https://prove2.me/theorems/48c6212f-295f-47f9-86bf-bb60d37ba811
-- title:
--   Theorem 3.5 — two-output rounding: E[max{A×, A_keep}] ≥ L + (13/17)G − 8ηF
-- statement:
--   Fix a feasible solution of the relaxation (with stored schedules and both density constraints), $\eta=1/q\le1/100$ and $K\ge1$.
--
--   1. With full consistency, Algorithm 1 returns a feasible schedule whose expected cardinality satisfies
--   $$\mathbb E[\max\{A_\times,A_{\mathrm{keep}}\}]\ge L+\frac{13}{17}G-8\eta F.$$
--   2. The same guarantee holds with projected consistency if $|J_{\mathrm{miss}}|\le\eta F$.
--
--   In both cases this holds for every maximal matching $\mathcal X$ of the crossing graph and every fixed tie-breaking; Algorithm 1's coordinated sample exists; every matching of the first sample and the coordinated schedule of the second sample are feasible on every outcome; and the bound holds for every coordinated joint law and every coupling of the two samples.
--
--   This is the rounding guarantee behind the $17/13+\varepsilon$ ratio.
--
--   **Formalization Note** Jobs and blocks have finite index types; expectations are finite weighted sums over the explicitly defined sampling outcomes.
--
--   Differences from the source:
--   - generalization: the coordinated sample of step 4 (Lemma 2.2’s construction) and two separately drawn samples → existence of a coordinated law, and the bound for every coordinated law and every coupling of the two samples; reason: the construction is such a law; p. 20: "No independence between the two output schedules is needed"
--   - generalization: "choose a maximal matching X" and "fixed tie-breaking" → every maximal matching and every rule choosing a boundary with the larger marginal; reason: the source leaves both choices unspecified
--   - encoding: "returns a feasible schedule" → every matching of an independent outcome yields a feasible schedule of its size, and the coordinated schedule is feasible on every outcome; reason: the returned schedule is one of the two
--   - generalization: the residual instance after discarding individually infeasible jobs in §2, with positive machine count and configuration cap → also permits jobs with processing time exceeding their window length, zero machines; reason: individually infeasible jobs occur in no feasible configuration or schedule; the extra zero cases have only empty configurations or zero marginals, and every source instance is included
-- source:
--   Tong and Xu, Coordinating Boundaries: Improved Approximation Algorithms for Unweighted Non-Preemptive Throughput Maximization, preprint of October 25, 2026 (STOC 2027 submission #141; source.pdf sha256 59f76539a5ee555f9e56603a067e9f858f38d003011e90b1716085348673687e), p. 20, Theorem 3.5 (Algorithm 1, p. 15)

import Mathlib
import Definitions.Def_CoordBoundaries_Throughput_Rounding

open Classical

namespace CoordBoundaries.Throughput

/-- **Theorem 3.5** (Tong–Xu, p. 20). Fix a feasible relaxation solution with the density
constraints, `η = 1/q ≤ 1/100` and `K ≥ 1`. With full consistency, Algorithm 1 (for every maximal
matching `𝒳` of the crossing graph and every fixed tie-breaking) returns a feasible schedule whose
expected cardinality satisfies `E[max{A×, A_keep}] ≥ L + (13/17)G − 8ηF`. The same guarantee holds
with projected consistency if `|J_miss| ≤ ηF`. -/
theorem theorem_3_5 {I : Instance} (hI : I.Valid) {P : Partition I.T} {K Δ q : ℕ}
    (hq : 100 ≤ q) (hK : 1 ≤ K) (hΔ : 1 ≤ Δ) (s : ConfigSol I P K)
    (hD₁ : s.DenseBlocks Δ q) (hD₂ : s.DenseSuper q) :
    (∀ π, s.FullConsistent π →
      ∀ X, s.IsMaximalCrossMatching X → ∀ side, s.SideRule side →
        s.AlgOneGuarantee X ∅ side (s.L + 13 / 17 * s.G - 8 * eta q * s.F)) ∧
    (∀ H π, s.ProjConsistent H π → ((s.JmissOf H).card : ℝ) ≤ eta q * s.F →
      ∀ X, s.IsMaximalCrossMatching X → ∀ side, s.SideRule side →
        s.AlgOneGuarantee X (s.JmissOf H) side (s.L + 13 / 17 * s.G - 8 * eta q * s.F)) := by sorry

end CoordBoundaries.Throughput

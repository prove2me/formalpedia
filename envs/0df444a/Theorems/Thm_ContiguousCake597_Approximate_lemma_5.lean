-- Prove2me | Theorems.Thm_ContiguousCake597_Approximate_lemma_5
-- name    : ContiguousCake597.Approximate.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:36.663352+00:00
-- url     : https://prove2.me/theorems/7cbb1d30-ef7f-4d00-b6ed-d9b6c115dc74
-- title:
--   Lemma 5 — density restrictions and total bonus, with §3.1 obligations
-- statement:
--   Let $G$ be any nonempty directed threshold-game graph in which every indegree is at most two. Form the sets, cycle, bonus intervals, valuations and normalized target exactly as defined in §3.1. Every density $f_i$ takes only the values 1 and 2 and has at most six breakpoints. For every interval $F\subseteq[0,L]$,
--   $$0\le U_i(F)-|F|\le6,\qquad U_i([0,L])=L+6.$$
--   The finite-overlap formula agrees with the interval integral of $f_i$; each such function is interval integrable. The source's unnumbered construction assertions also hold: block sizes are at least 20, bin occupancy is at most $R-8$, the sets have the cardinalities and prefix counts in (S1), and the cycle and its neighboring indices satisfy (S2). The normalized target is a valid restricted instance and obeys
--   $$V_i([a,b])=\frac{U_i([La,Lb])}{L+6}.$$
--   Every real-cut complete $\varepsilon$-envy-free allocation scales to an $\eta$-envy-free allocation of $[0,L]$, with its assignment unchanged. These assertions make the actual construction available to the later lemmas without assuming its properties.
--
--   Differences from the source:
--   - encoding: Lemma 5 with the unnumbered construction and normalization facts of §3.1 → one conjunction containing the full Lemma 5, (S1)/(S2), the block bounds, integral agreement and normalization/scaling facts; reason: exposes all supporting obligations as conclusions without adding a numbered milestone or assuming any proved construction fact
--   - encoding: bonus intervals and density endpoint values on the cake → right-continuous half-open bonus indicators, extended as baseline 1 outside the cake; reason: endpoints have zero mass; the extension makes interval integrals total without changing any cake valuation
-- source:
--   Yasushi Kawase, Bodhayan Roy, Mohammad Azharuddin Sanpui, STOC 2027 submission #597 (October 2026), p. 7 (PDF 8), Lemma 5, §3.1 pp.5–8 (PDF 6–9)

import Definitions.Def_ContiguousCake597_Approximate_Analysis

namespace ContiguousCake597.Approximate

/-- Lemma 5, printed p.7 (PDF 8). The conjunction also exposes the
unnumbered S1/S2 and target-normalization obligations of §3.1; none is a hypothesis. -/
theorem lemma_5 (G : HZTractability.ThrGraph) (hn : 1 ≤ G.n)
    (hdeg : ∀ v, G.indeg v ≤ 2) :
    ConstructionFacts G ∧
    (∀ i : Fin (N G),
      (∀ t : ℝ, f G i t = 1 ∨ f G i t = 2) ∧
      HasAtMostBreakpoints (f G i) 6 ∧
      (∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ (L G : ℝ) →
        0 ≤ U G i x y - (y-x) ∧ U G i x y - (y-x) ≤ 6) ∧
      U G i 0 (L G : ℝ) = (L G : ℝ)+6 ∧
      (∀ x y : ℝ, x ≤ y →
        IntervalIntegrable (f G i) MeasureTheory.volume x y ∧
        U G i x y = ∫ t in x..y, f G i t)) ∧
    TargetFacts G := by sorry

end ContiguousCake597.Approximate

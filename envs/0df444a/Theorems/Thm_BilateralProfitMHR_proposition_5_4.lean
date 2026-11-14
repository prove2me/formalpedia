-- Prove2me | Theorems.Thm_BilateralProfitMHR_proposition_5_4
-- name    : BilateralProfitMHR.proposition_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:20:08.664214+00:00
-- url     : https://prove2.me/theorems/f195f949-c9e6-4231-b957-7bdab90a7df4
-- title:
--   Proposition 5.4 — simultaneous concentration $|\hat\mu(e)-\mu(e)|\le(\mu(e)+\delta)/16$ with probability $1-1/T$
-- statement:
--   Let $2\le K\le T$, and run Initialize mhr (Algorithm 4) on fresh i.i.d. valuations from a product law $\mathcal D_s\times\mathcal D_b$ whose densities are strictly positive on $[0,1]$. With probability at least $1-1/T$, simultaneously at every scale $\delta$ reached by the procedure, the estimates computed at that scale satisfy
--   $$|\hat\mu(e)-\mu(e)|\le\frac{\mu(e)+\delta}{16}\qquad\text{for every }e\in G_K.\tag{29}$$
--   Here $G_K$ is the triangle grid and the reached scales are those tested up to and including the trigger.
--
--   This clean event is the one on which the guarantees of Lemma 5.3 are proved.
--
--   Differences from the source:
--   - generalization: the MHR distributions of §5 → every independent pair with strictly positive densities on $[0,1]$; reason: the proof (pp.59–60) uses only independence and monotonicity of $P$; the statement specializes to the MHR class
--   - reading: "the first recursive split separating $i$ and $j$" → the midpoint $k$ of the smallest bisection interval containing both, so $i\le k<j$; reason: the bisection rule is not spelled out; this is the reading under which the proof holds as printed ("The construction includes $(i,k)$, $(k,j)$, and $(k,k)$ in $S$", p.60)
--   - encoding: posting each pair for $N$ fresh rounds → an array of independent samples indexed by (scale, grid pair, repetition); reason: the run at a scale reads only that scale's samples, so every event about the run has the same probability
--   - encoding: "with probability at least $1-1/T$" → a measurable event of probability at least $1-1/T$ on which (29) holds at every reached scale; reason: same statement, stated without outer measure
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Proposition 5.4, p.33 (PDF 35); proof App. A.5, pp.59–60 (PDF 61–62)

import Mathlib
import Definitions.Def_BilateralProfitMHR_InitializeMHR

namespace BilateralProfitMHR

open MeasureTheory BilateralProfit MechanismDesign.BilateralTrade
open scoped ENNReal

/-- **Proposition 5.4 (Simultaneous concentration)**, Brüstle, di Gregorio, Fusco, Leonardi
(manuscript, sha256 e91e8127…), p.33 (PDF 35); proof App. A.5, pp.59–60 (PDF 61–62): let
`2 ≤ K ≤ T`. With probability at least `1 − 1/T`, simultaneously at every scale `δ` reached by
Initialize mhr, the estimates computed at that scale satisfy
`|µ̂(e) − µ(e)| ≤ (µ(e) + δ)/16` for every `e ∈ G_K` (29).

**Formalization Note.** `G_K` is Algorithm 4's triangle grid `Act K`; the reached scales are
`testedScales` (up to and including the trigger). The probability is over the fresh probing
valuations, i.i.d. with law `E.prior` (`initLaw`); "with probability at least `1 − 1/T`" is a
measurable event of that probability on which the bounds hold. Stated for every independent
pair of laws with positive densities on `[0, 1]`, MHR or not (the proof uses only independence
and monotonicity). -/
theorem proposition_5_4 (T K : ℕ) (hK : 2 ≤ K) (hKT : K ≤ T) (E : Environment)
    (hE : UnitSupport E) :
    ∃ G : Set (Samples K T), MeasurableSet G ∧ 1 - (T : ℝ≥0∞)⁻¹ ≤ initLaw K T E.prior G ∧
      ∀ ω ∈ G, ∀ h ∈ testedScales K T ω, ∀ e : Act K,
        |muHat K T h ω e - muP E.prior (pt K e.1)| ≤ (muP E.prior (pt K e.1) + delta h) / 16 := by sorry

end BilateralProfitMHR

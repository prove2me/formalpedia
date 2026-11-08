-- Prove2me | Theorems.Thm_CausalFailureRank_lower_bound
-- name    : CausalFailureRank.lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:16:12.893524+00:00
-- url     : https://prove2.me/theorems/c1dcf4f5-20c8-4daf-9d7a-0a7e3e382ceb
-- title:
--   App. B.3 — the lower comparison $G_{1,U}(1/\delta)-1$
-- statement:
--   For a $\delta$-safe policy with $\delta>0$, under every contract and all caps, the expected actual charges satisfy
--   $$\mathbb E[C]\ge G_{1,U}(1/\delta)-1.$$
--   This is the lower bound of the price law, for the full comparator class.
--
--   Differences from the source:
--   - encoding: stages $1,\dots,N+1$ → 0-based stages, terminal $i\ge N$; reason: Lean indexing; no instance changes
--   - generalization: rational probabilities, fees and risk parameters → real ones; reason: rationality serves only computability, which is not claimed here; the rational case is an instance
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), App. B.3, p.17

import Mathlib
import Definitions.Def_CausalFailureRank_G
import Definitions.Def_CausalFailureRank_V

open Filter Topology MeasureTheory

namespace CausalFailureRank

variable {N q : ℕ}

/-- **The lower comparison.** Zang, Li, Jin, Xu, *Causal Failure Rank Determines Statistical Depth*, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), App. B.3, p.17: "For a δ-safe native policy take λ = 1/δ in the
bridge. Its actual variable cost is at least G_{1,U}(1/δ) − 1, proving the lower bound in Theorem 3.1
for the full comparator."

**Formalization Note.** For every lawful randomized policy, every contract and all caps. -/
theorem lower_bound (I : Instance N q) (κ : Contract) (caps : Caps N) (p : Policy I) (δ : ℝ) (hδ : 0 < δ)
    (hsafe : failProb I κ caps p ≤ ENNReal.ofReal δ) :
    ENNReal.ofReal (G I 0 Finset.univ (1 / δ) - 1) ≤ expBill I κ caps p := by sorry

end CausalFailureRank

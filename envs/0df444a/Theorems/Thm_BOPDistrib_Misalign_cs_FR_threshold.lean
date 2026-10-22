-- Prove2me | Theorems.Thm_BOPDistrib_Misalign_cs_FR_threshold
-- name    : BOPDistrib.Misalign.cs_FR_threshold
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:35.573574+00:00
-- url     : https://prove2.me/theorems/1172ba50-d924-4f5b-8ba1-08564b8fbeaa
-- title:
--   Proof of Proposition 2, p. 47 (PDF 48) — CS^FR ≥ CS^F iff α ≥ a_4(m)
-- statement:
--   Under the standing assumptions at ATP $m$, there is a threshold $a_4(m)\in[0,\infty]$ such that for every risk aversion $\alpha>0$
--   $$CS^{FR}(\alpha)\ \ge\ CS^F\iff\alpha\ge a_4(m).$$
--
--   Together with $CS^{MR}\ge CS^M\ge CS^F$, this threshold is exactly where F induces the smallest consumer surplus.
--
--   **Formalization Note** The threshold is fixed before $\alpha$, so the set of such $\alpha$ is a closed upward ray in $(0,\infty)$. Its closedness at the left endpoint uses FR's tie-break $y\le y_\theta$.
-- source:
--   Calmon, Jue-Rajasingh, Romero & Stenson, Operational strategies for distributing durable goods in the base of the pyramid, accepted manuscript (M&SOM 24(4), 2022; TSpace, SSRN 2882402), p. 47 (PDF 48), proof of Proposition 2

import Mathlib
import Definitions.Def_BOPDistrib_Misalign_Model

namespace BOPDistrib.Misalign

/-- Proof of Proposition 2 (p. 47): there is a threshold `a₄(m) ∈ [0, ∞]` such that, for every
`α > 0`, `CS^FR ≥ CS^F` if and only if `α ≥ a₄(m)`. -/
theorem cs_FR_threshold (P : Params) (m : ℝ) (hS : Standing P m) :
    ∃ a4 : ENNReal, ∀ α : ℝ, 0 < α → (CSF P m ≤ CSFR P m α ↔ a4 ≤ ENNReal.ofReal α) := by sorry

end BOPDistrib.Misalign

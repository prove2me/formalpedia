-- Prove2me | Theorems.Thm_BOPDistrib_Misalign_property_4
-- name    : BOPDistrib.Misalign.property_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:24.00272+00:00
-- url     : https://prove2.me/theorems/852c03dc-8ae5-4f49-a0d9-f7a619034dbd
-- title:
--   Property 4, p. 41 (PDF 42), proof pp. 43–44 — Π^F_D ≥ Π^FR_D iff α ≥ a_3(m)
-- statement:
--   Under the standing assumptions at ATP $m$, there is a threshold $a_3(m)\in[0,\infty]$ such that for every risk aversion $\alpha>0$
--   $$\Pi^F_D\ \ge\ \Pi^{FR}_D(\alpha)\iff \alpha\ge a_3(m).$$
--   The value $a_3(m)=\infty$ means that FR beats F at every $\alpha$.
--
--   Higher risk aversion makes the refund needed to sell to uninformed customers more expensive. Past $a_3(m)$, F therefore dominates the finance strategy with returns.
--
--   **Formalization Note** The threshold is fixed before $\alpha$ is quantified, so the statement asserts that the set of $\alpha$ where F beats FR is a closed upward ray in $(0,\infty)$. The paper's hypotheses $w\le\bar w$ and $c_\theta\le\bar c_\theta$ are not needed and are not assumed.
-- source:
--   Calmon, Jue-Rajasingh, Romero & Stenson, Operational strategies for distributing durable goods in the base of the pyramid, accepted manuscript (M&SOM 24(4), 2022; TSpace, SSRN 2882402), p. 41 (PDF 42), Property 4; pp. 43–44 (PDF 44–45), proof of Property 4

import Mathlib
import Definitions.Def_BOPDistrib_Misalign_Model

namespace BOPDistrib.Misalign

/-- Property 4 (p. 41, proof pp. 43–44): there is a threshold `a₃(m) ∈ [0, ∞]` such that, for every
risk aversion `α > 0`, `Π^F_D ≥ Π^FR_D` if and only if `α ≥ a₃(m)`. -/
theorem property_4 (P : Params) (m : ℝ) (hS : Standing P m) :
    ∃ a3 : ENNReal, ∀ α : ℝ, 0 < α → (PiFR P m α ≤ PiF P m ↔ a3 ≤ ENNReal.ofReal α) := by sorry

end BOPDistrib.Misalign

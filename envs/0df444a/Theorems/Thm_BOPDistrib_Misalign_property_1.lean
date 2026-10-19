-- Prove2me | Theorems.Thm_BOPDistrib_Misalign_property_1
-- name    : BOPDistrib.Misalign.property_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:28.105227+00:00
-- url     : https://prove2.me/theorems/dc6bd43c-e8eb-44e7-bbf5-9783fce6b597
-- title:
--   Property 1, p. 41 (PDF 42) — Π^F_D ≥ Π^M_D iff m ≤ m^F
-- statement:
--   Under the standing assumptions, strategy F (subsidy first, no returns) earns at least as much as strategy M (education first, no returns) exactly when the ATP is at most $m^F$:
--   $$\Pi^F_D\ \ge\ \Pi^M_D\iff m\le m^F=\frac{c_\theta/\beta+w-\gamma v_h}{1-\gamma}.$$
--
--   This is the ATP threshold that separates the finance-based strategies from the marketing-based ones in the strategy map of Proposition B.2.
--
--   **Formalization Note** Neither value depends on $\alpha$. The strict Assumption 1, $b>0$ and $m<v_h$ make $\theta^F<\theta^M$, so the comparison is not degenerate. The paper's hypotheses $w\le\bar w$ and $c_\theta\le\bar c_\theta$ are not needed and are not assumed.
-- source:
--   Calmon, Jue-Rajasingh, Romero & Stenson, Operational strategies for distributing durable goods in the base of the pyramid, accepted manuscript (M&SOM 24(4), 2022; TSpace, SSRN 2882402), p. 41 (PDF 42), proof of Proposition B.2, Property 1 and its proof

import Mathlib
import Definitions.Def_BOPDistrib_Misalign_Model

namespace BOPDistrib.Misalign

/-- Property 1 (proof of Proposition B.2, p. 41): `Π^F_D ≥ Π^M_D` if and only if `m ≤ m^F`,
with `m^F = (cθ/β + w − γ v_h)/(1 − γ)`. -/
theorem property_1 (P : Params) (m : ℝ) (hS : Standing P m) :
    PiM P m ≤ PiF P m ↔ m ≤ mF P := by sorry

end BOPDistrib.Misalign

-- Prove2me | Theorems.Thm_BOPDistrib_Misalign_property_6
-- name    : BOPDistrib.Misalign.property_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:22.812153+00:00
-- url     : https://prove2.me/theorems/b6815979-77fc-4ec5-82b3-4c4fd48b59e9
-- title:
--   Property 6, p. 41 (PDF 42) — when m ≤ m^F, Π^MR_D ≤ max(Π^FR_D, Π^M_D)
-- statement:
--   Under the standing assumptions, if the ATP satisfies $m\le m^F$, then for every risk aversion $\alpha>0$
--   $$\Pi^{MR}_D(\alpha)\ \le\ \max\big(\Pi^{FR}_D(\alpha),\ \Pi^M_D\big).$$
--
--   At low ATP the education-first strategy with returns is never the unique best. Together with Properties 1 and 4 this reduces "F is optimal" to $m\le m^F$ and $\alpha\ge a_3(m)$.
--
--   **Formalization Note** The paper's hypotheses $w\le\bar w$ and $c_\theta\le\bar c_\theta$ are not needed and are not assumed.
-- source:
--   Calmon, Jue-Rajasingh, Romero & Stenson, Operational strategies for distributing durable goods in the base of the pyramid, accepted manuscript (M&SOM 24(4), 2022; TSpace, SSRN 2882402), p. 41 (PDF 42), proof of Proposition B.2, Property 6

import Mathlib
import Definitions.Def_BOPDistrib_Misalign_Model

namespace BOPDistrib.Misalign

/-- Property 6 (p. 41): when `m ≤ m^F`, `Π^MR_D ≤ max(Π^FR_D, Π^M_D)` for every `α > 0`. -/
theorem property_6 (P : Params) (m : ℝ) (hS : Standing P m) (hm : m ≤ mF P) :
    ∀ α : ℝ, 0 < α → PiMR P m α ≤ max (PiFR P m α) (PiM P m) := by sorry

end BOPDistrib.Misalign

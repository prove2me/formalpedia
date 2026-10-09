-- Prove2me | Theorems.Thm_CompositeLB_DetLip_query_count
-- name    : CompositeLB.DetLip.query_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:34:18.321149+00:00
-- url     : https://prove2.me/theorems/f74d7167-a08c-4b7e-ad29-97c9025360f8
-- title:
--   Appendix B.1, p. 12: the round and query thresholds imply m/(48ε)
-- statement:
--   For an integer $m\ge1$ and $0<\varepsilon\le1/12$, the two query thresholds in Appendix B.1 obey
--
--   $$\min\left\{\frac m\varepsilon,\ \left\lfloor\frac1{12\varepsilon}\right\rfloor\left\lceil\frac m2\right\rceil\right\}\ge\frac m{48\varepsilon}.$$
--
--   It converts the number of completed rounds into the explicit query lower bound for the normalized hard instance.
--
--   **Formalization Note** Floors and ceilings are natural numbers cast to real numbers. The main theorem itself retains an unspecified absolute Ω constant because the printed hard function is not 1-Lipschitz without rescaling.
-- source:
--   Woodworth & Srebro, arXiv:1605.08003v3, App. B.1, p. 12, query-count display before Lemma 2

import Mathlib
import Definitions.Def_CompositeLB_DetLip_Model

namespace CompositeLB.DetLip

/-- Appendix B.1, p. 12: the two stopping thresholds both give enough queries. -/
theorem query_count (m : ℕ) (ε : ℝ) (hm : 1 ≤ m)
    (hε : 0 < ε) (hε_bound : ε ≤ 1 / 12) :
    (m : ℝ) / (48 * ε) ≤
      min ((m : ℝ) / ε)
        (((⌊1 / (12 * ε)⌋₊ : ℕ) : ℝ) *
          ((⌈(m : ℝ) / 2⌉₊ : ℕ) : ℝ)) := by sorry

end CompositeLB.DetLip

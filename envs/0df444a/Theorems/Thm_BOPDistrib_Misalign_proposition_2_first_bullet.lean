-- Prove2me | Theorems.Thm_BOPDistrib_Misalign_proposition_2_first_bullet
-- name    : BOPDistrib.Misalign.proposition_2_first_bullet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:23.204524+00:00
-- url     : https://prove2.me/theorems/92747dc6-443e-4f33-b2e6-dfb878567ac0
-- title:
--   Proposition 2, first bullet, p. 17 (PDF 18) — MR induces the largest consumer surplus; CS^MR ≥ CS^M ≥ CS^F
-- statement:
--   Under the standing assumptions, for every risk aversion $\alpha>0$, strategy MR (education first, with returns) induces the largest consumer surplus among the four strategies of Theorem 1. Moreover,
--   $$CS^{MR}\ \ge\ CS^M\ \ge\ CS^F,\qquad CS^{MR}\ge CS^{FR}.$$
--
--   This holds at every ATP and every risk aversion, so the surplus-maximizing strategy never changes. The misalignment with profit therefore comes only from where profit-optimality lies.
--
--   **Formalization Note** The page says $\alpha\ge0$; $\alpha>0$ is required because $r_\alpha$ divides by $\alpha$.
-- source:
--   Calmon, Jue-Rajasingh, Romero & Stenson, Operational strategies for distributing durable goods in the base of the pyramid, accepted manuscript (M&SOM 24(4), 2022; TSpace, SSRN 2882402), p. 17 (PDF 18), Proposition 2, first bullet; p. 47 (PDF 48), proof of Proposition 2

import Mathlib
import Definitions.Def_BOPDistrib_Misalign_Model

namespace BOPDistrib.Misalign

/-- Proposition 2, first bullet (p. 17): for every `α > 0`, strategy MR induces the largest consumer
surplus among F, M, FR, MR, and `CS^MR ≥ CS^M ≥ CS^F`. -/
theorem proposition_2_first_bullet (P : Params) (m α : ℝ) (hS : Standing P m) (hα : 0 < α) :
    MRMaxCS P m α ∧ CSF P m ≤ CSM P m ∧ CSM P m ≤ CSMR P m α := by sorry

end BOPDistrib.Misalign

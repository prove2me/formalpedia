-- Prove2me | Theorems.Thm_DeferredInspection_SingleAgent_proposition_3
-- name    : DeferredInspection.SingleAgent.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:15.866062+00:00
-- url     : https://prove2.me/theorems/13b88bb9-a594-42af-a841-c180067f2e6d
-- title:
--   Proposition 3, p. 11 — unique and monotone best-alternative bid, corrected
-- statement:
--   For an SCD allocation $x$ with threshold $\bar v$, the minimizing report in (10) is unique at every value. Its best-alternative bid $b_x$ is nondecreasing, vanishes through a lower threshold $\underline v$, and is strictly increasing while $b_x(v)<\bar v$:
--
--   $$b_x(v)=0\quad(0\le v\le\underline v),\qquad
--   b_x\text{ strictly increases wherever }\underline v\le v\le1
--   \text{ and }b_x(v)<\bar v.$$
--
--   This describes the bidding geometry needed for the explicit mechanism.
--
--   **Formalization Note** The page's strict increase on the entire interval can fail after the bid reaches $\bar v$: $x(v)=4v-v^2$ up to $2-\sqrt3$, and one afterward, has a flat bid segment. The proof's claim $b_x(1)=\bar v$ also fails for $x(v)=1-(1-v)^2$, where $\bar v=1$ and $b_x(1)=1/2$. The dependent converse is omitted.
-- source:
--   Alaei, Belloni, Makhdoumi & Malekian, SSRN 3700525 (version of 2022-03-22), p. 11, Proposition 3; proof pp. 30–32, corrected as noted

import Mathlib
import Definitions.Def_DeferredInspection_SingleAgent_Model

namespace DeferredInspection.SingleAgent

open MeasureTheory Set Filter Topology

theorem proposition_3 (x : ℝ → ℝ) (vh : ℝ) (hx : IsSCD x vh) :
    (∀ v ∈ Icc (0 : ℝ) 1,
      ∃! u, u ∈ Icc 0 v ∧
        IsMinOn (fun w => v * (x v - x w) + w) (Icc 0 v) u) ∧
    MonotoneOn (bestAltOf x) (Icc 0 1) ∧
    ∃ vl ∈ Icc (0 : ℝ) 1,
      (∀ v ∈ Icc 0 vl, bestAltOf x v = 0) ∧
      StrictMonoOn (bestAltOf x)
        {v | vl ≤ v ∧ v ≤ 1 ∧ bestAltOf x v < vh} := by sorry

end DeferredInspection.SingleAgent

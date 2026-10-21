-- Prove2me | Theorems.Thm_EpiControl_SinglePeak_lemma_9_existence
-- name    : EpiControl.SinglePeak.lemma_9_existence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:25.226562+00:00
-- url     : https://prove2.me/theorems/d0c80090-d1bc-46b3-8e38-fde68c1b1433
-- title:
--   Lemma 9 (first part), p. 15 (PDF 16) — an optimal social-distancing policy exists
-- statement:
--   Consider the controlled SIR model with transmission rate $\beta(t)\in B=[\underline b,\bar b]$, recovery rate $\gamma>0$, horizon $T>0$ and the cost
--   $$J(\beta)=\int_0^T \big(v(i(t))+c(\beta(t))\big)\,dt+\bar v(i(T)),\qquad \bar v(x)=\int_0^x\frac{v(z)}{z\gamma}\,dz,$$
--   under the standing assumptions of §2. Then there is an admissible control $\beta^*$ with SIR path $(s^*,i^*)$ that minimizes $J$ over all admissible controls:
--   $$\beta^*\in\arg\min_{\beta\in\mathcal B}J(\beta).$$
--
--   This is the existence half of Proposition 1; it guarantees that the statements about optimal policies in this mission are not vacuous.
--
--   **Formalization Note** "Optimal" compares $J$ with every admissible control together with every SIR path it drives (paths are unique, so this is the page's $J(\beta)$).
-- source:
--   Kruse & Strack, Optimal Control of an Epidemic through Social Distancing, Cowles Foundation Discussion Paper No. 2229R (rev. July 2020), p. 15 (PDF 16), Lemma 9, first sentence

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model

open MeasureTheory Set Filter Topology

namespace EpiControl.SinglePeak

theorem lemma_9_existence (P : Params) (hP : P.Standing) :
    ∃ β s i : ℝ → ℝ, P.IsOptimal β s i := by sorry
end EpiControl.SinglePeak

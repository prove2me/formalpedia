-- Prove2me | Theorems.Thm_Arxiv1504_01000_sdY4O_negative_powers
-- name    : Arxiv1504_01000.sdY4O_negative_powers
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T19:41:09.932627+00:00
-- url     : https://prove2.me/theorems/b3b5b3f3-6828-4774-b509-00115bed9bf0
-- title:
--   Section V: SD-Y4O adds non-negative amounts to negative double-bounce and surface powers
-- statement:
--   Let $P_s,P_d,P_v,P_c$ be the Y4O powers of a pixel with $P_v\ge0$, let $0\le\delta\le1$, and let $\tfrac12\le\alpha\le1$, $0\le\beta\le\tfrac12$ with $\alpha+\beta=1$. Then the amounts $\alpha P_v\delta$ and $\beta P_v\delta$ that SD-Y4O adds to the double-bounce and surface powers are non-negative, so $P_d^n\ge P_d$ and $P_s^n\ge P_s$. A negative power becomes non-negative exactly when its magnitude is at most the amount added:
--
--   $$P_d^n<0\iff P_d<-\alpha P_v\delta,\qquad P_s^n<0\iff P_s<-\beta P_v\delta.$$
--
--   So small negative powers are made non-negative, and large negative powers remain negative.
--
--   **Formalization Note** The paper's "small" and "large" negative powers are made precise by the threshold, the amount added. The paper calls the added amounts positive. They are non-negative under the stated ranges, and positive when $P_v,\delta,\beta>0$. The assumption $P_v\ge0$ is implicit in the paper.
-- source:
--   Bhattacharya, Muhuri, De, Manickam and Frery, Modifying the Yamaguchi Four-Component Decomposition Scattering Powers Using a Stochastic Distance, arXiv:1504.01000v1 (2015), claim c019 (a); Sec. V (Results and Discussion), paragraph on negative powers before Table IV, PDF p. 7

import Mathlib
import Definitions.Def_Arxiv1504_01000_Basic

open MeasureTheory Filter Topology
open scoped ComplexOrder

namespace Arxiv1504_01000

theorem sdY4O_negative_powers (P : Y4OPowers) (δ α β : ℝ) (hPv : 0 ≤ P.pv) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hα : 1 / 2 ≤ α ∧ α ≤ 1) (hβ : 0 ≤ β ∧ β ≤ 1 / 2) (hαβ : α + β = 1) :
    0 ≤ α * P.pv * δ ∧ 0 ≤ β * P.pv * δ ∧
    P.pd ≤ (sdY4O P δ α β).pd ∧ P.ps ≤ (sdY4O P δ α β).ps ∧
    ((sdY4O P δ α β).pd < 0 ↔ P.pd < -(α * P.pv * δ)) ∧
    ((sdY4O P δ α β).ps < 0 ↔ P.ps < -(β * P.pv * δ)) := by sorry

end Arxiv1504_01000

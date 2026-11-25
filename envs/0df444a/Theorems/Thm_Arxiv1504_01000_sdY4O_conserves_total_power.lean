-- Prove2me | Theorems.Thm_Arxiv1504_01000_sdY4O_conserves_total_power
-- name    : Arxiv1504_01000.sdY4O_conserves_total_power
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T19:30:41.27308+00:00
-- url     : https://prove2.me/theorems/9e898b2d-1f82-48be-9a8a-adb245297bfe
-- title:
--   Eqs. (13a)-(13d): SD-Y4O conserves the total power
-- statement:
--   Let $P_s,P_d,P_v,P_c$ be the Y4O surface, double-bounce, volume and helix powers of a pixel, let $0\le\delta\le1$ (the maximum relative Hellinger distance $\delta_H^m$), and let $\tfrac12\le\alpha\le1$, $0\le\beta\le\tfrac12$ with $\alpha+\beta=1$. The SD-Y4O powers of eqs. (13a)-(13d) are
--
--   $$P_v^n=P_v(1-\delta),\quad P_d^n=P_d+\alpha P_v\delta,\quad P_s^n=P_s+\beta P_v\delta,\quad P_c^n=P_c.$$
--
--   They conserve the total power, $P_s^n+P_d^n+P_v^n=P_s+P_d+P_v$, and also the four-component sum including $P_c$. The linear map $\alpha(\phi)=\tfrac12+2\phi/\pi$ takes $[0,\pi/4]$ onto $[\tfrac12,1]$, with $\alpha(0)=\tfrac12$ and $\alpha(\pi/4)=1$. For $\phi\in[0,\pi/4]$, $\alpha(\phi)$ and $\beta=1-\alpha(\phi)$ satisfy the ranges above.
--
--   **Formalization Note** The paper calls $\alpha$ and $\beta$ positive but allows $\beta=0$. The ranges $0.5\le\alpha\le1$ and $0\le\beta\le0.5$ are used as stated. The paper does not say which way the map onto $[0.5,1]$ runs; it is taken increasing.
-- source:
--   Bhattacharya, Muhuri, De, Manickam and Frery, Modifying the Yamaguchi Four-Component Decomposition Scattering Powers Using a Stochastic Distance, arXiv:1504.01000v1 (2015), claim c007; Sec. IV, eqs. (13a)-(13d) and the two paragraphs after them, PDF p. 5

import Mathlib
import Definitions.Def_Arxiv1504_01000_Basic

open MeasureTheory Filter Topology
open scoped ComplexOrder

namespace Arxiv1504_01000

theorem sdY4O_conserves_total_power (P : Y4OPowers) (δ α β : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hα : 1 / 2 ≤ α ∧ α ≤ 1) (hβ : 0 ≤ β ∧ β ≤ 1 / 2) (hαβ : α + β = 1) :
    (sdY4O P δ α β).ps + (sdY4O P δ α β).pd + (sdY4O P δ α β).pv = P.ps + P.pd + P.pv ∧
    (sdY4O P δ α β).ps + (sdY4O P δ α β).pd + (sdY4O P δ α β).pv + (sdY4O P δ α β).pc =
      P.ps + P.pd + P.pv + P.pc ∧
    (∀ φ ∈ Set.Icc (0 : ℝ) (Real.pi / 4),
      1 / 2 ≤ alphaOfOA φ ∧ alphaOfOA φ ≤ 1 ∧ 0 ≤ 1 - alphaOfOA φ ∧ 1 - alphaOfOA φ ≤ 1 / 2) ∧
    alphaOfOA 0 = 1 / 2 ∧ alphaOfOA (Real.pi / 4) = 1 ∧
    alphaOfOA '' Set.Icc (0 : ℝ) (Real.pi / 4) = Set.Icc (1 / 2 : ℝ) 1 := by sorry

end Arxiv1504_01000

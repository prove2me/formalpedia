-- Prove2me | Theorems.Thm_Arxiv2405_02007_new_degree_of_polarisation
-- name    : Arxiv2405_02007.new_degree_of_polarisation
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T16:57:47.069359+00:00
-- url     : https://prove2.me/theorems/4fb6fca2-1f9d-4b72-95b0-2cfe4b12f51e
-- title:
--   Eq. (12): the new degree of polarisation
-- statement:
--   Let a pixel have total power $\mathrm{Span}>0$ and degree of polarisation $m_{FP}\in[0,1]$, with volume power $P_v=(1-m_{FP})\,\mathrm{Span}$. Suppose the volume power changes by $\Delta P_v$ and the new volume power $P_v'=P_v+\Delta P_v$ is expressed through a new degree of polarisation $m_{FP}'$ by eq. (2) with the same $\mathrm{Span}$:
--
--   $$P_v+\Delta P_v=(1-m_{FP}')\cdot\mathrm{Span}.$$
--
--   Then
--
--   $$m_{FP}'=\frac{\mathrm{Span}-P_v-\Delta P_v}{\mathrm{Span}}.$$
--
--   This is the step from eq. (11) to eq. (12) of the paper, used to compute the helix power after the volume correction.
--
--   **Formalization Note** The total power is the same before and after the correction, as in eq. (11). No range is imposed on $m_{FP}'$, since the paper imposes none.
-- source:
--   J. D. Ballester-Berman, Analysing PolSAR data from vegetation by using the subaperture decomposition approach, arXiv:2405.02007v1 (2024), claim c024; Section 5.1, eqs. (10)-(12), PDF p. 18

import Mathlib
import Definitions.Def_Arxiv2405_02007_Basic

open Real

namespace Arxiv2405_02007

theorem new_degree_of_polarisation (span m m' dPv : ℝ) (hspan : 0 < span) (hm0 : 0 ≤ m)
    (hm1 : m ≤ 1) (h11 : volumePower m' span = volumePower m span + dPv) :
    m' = (span - volumePower m span - dPv) / span := by sorry

end Arxiv2405_02007

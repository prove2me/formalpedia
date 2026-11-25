-- Prove2me | Theorems.Thm_Arxiv2405_02007_helix_power_after_volume_correction
-- name    : Arxiv2405_02007.helix_power_after_volume_correction
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T17:06:48.179399+00:00
-- url     : https://prove2.me/theorems/f4dbd495-ba33-597b-a61e-c4d2c69ae069
-- title:
--   Eq. (15): the helix power after a change of the volume power
-- statement:
--   Let a pixel have total power $\mathrm{Span}>0$, degree of polarisation $0<m_{FP}\le1$ and scattering asymmetry parameter $\tau_{FP}\in\mathbb R$, with volume power $P_v=(1-m_{FP})\,\mathrm{Span}$ and helix power $P_c=m_{FP}\,\mathrm{Span}\,\sin(2\tau_{FP})$. Let the volume power change by $\Delta P_v$, with the new degree of polarisation $m_{FP}'$ given by $P_v+\Delta P_v=(1-m_{FP}')\,\mathrm{Span}$ (eq. 11), and let the new helix power be $P_c'=m_{FP}'\,\mathrm{Span}\,\sin(2\tau_{FP})$ (eq. 9 with the same $\mathrm{Span}$ and $\tau_{FP}$). Then:
--
--   1. the new helix power is
--   $$P_c'=P_c\cdot\left(1-\frac{\Delta P_v}{\mathrm{Span}-P_v}\right);$$
--   2. if $P_c>0$, then $P_c'>P_c$ when $\Delta P_v<0$, and $P_c'<P_c$ when $\Delta P_v>0$.
--
--   So a correction that lowers the volume power raises the helix power, and conversely.
--
--   **Formalization Note** Three hypotheses are implicit in the paper and are written explicitly: $\mathrm{Span}$ and $\tau_{FP}$ are unchanged by the correction (the paper substitutes the old $\sin(2\tau_{FP})$ of eq. (14) into eq. (9)); $m_{FP}>0$, so that $\mathrm{Span}-P_v=m_{FP}\,\mathrm{Span}\ne0$; and $P_c>0$ in part 2, since $P_c'-P_c=-\Delta P_v\sin(2\tau_{FP})$: if $P_c=0$ the two powers are equal, and if $P_c<0$ (possible for an arbitrary real $\tau_{FP}$) the comparison is reversed. In Dey et al. (2021) $\tau_{FP}\in[0^\circ,45^\circ]$, so $P_c\ge0$ and $P_c>0$ is the paper's non-degenerate case.
-- source:
--   J. D. Ballester-Berman, Analysing PolSAR data from vegetation by using the subaperture decomposition approach, arXiv:2405.02007v1 (2024), claim c024; Section 5.1, eqs. (9)-(15) and the sentence after eq. (15), PDF pp. 18-19

import Mathlib
import Definitions.Def_Arxiv2405_02007_Basic

open Real

namespace Arxiv2405_02007

theorem helix_power_after_volume_correction (span m tau m' dPv : ℝ) (hspan : 0 < span)
    (hm0 : 0 < m) (hm1 : m ≤ 1) (h11 : volumePower m' span = volumePower m span + dPv) :
    helixPower m' span tau = helixPower m span tau * (1 - dPv / (span - volumePower m span)) ∧
    (0 < helixPower m span tau →
      (dPv < 0 → helixPower m span tau < helixPower m' span tau) ∧
      (0 < dPv → helixPower m' span tau < helixPower m span tau)) := by sorry

end Arxiv2405_02007

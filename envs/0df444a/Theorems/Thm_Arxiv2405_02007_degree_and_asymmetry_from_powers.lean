-- Prove2me | Theorems.Thm_Arxiv2405_02007_degree_and_asymmetry_from_powers
-- name    : Arxiv2405_02007.degree_and_asymmetry_from_powers
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T17:02:58.449561+00:00
-- url     : https://prove2.me/theorems/5b344fb8-e4e2-451d-b58c-0afd1ebf2fbf
-- title:
--   Eqs. (13)-(14): the degree of polarisation and $\sin(2\tau_{FP})$ from the powers
-- statement:
--   Let a pixel have total power $\mathrm{Span}>0$, degree of polarisation $0<m_{FP}\le1$ and scattering asymmetry parameter $\tau_{FP}\in\mathbb R$, with volume power $P_v=(1-m_{FP})\,\mathrm{Span}$ and helix power $P_c=m_{FP}\,\mathrm{Span}\,\sin(2\tau_{FP})$. Then
--
--   $$m_{FP}=\frac{\mathrm{Span}-P_v}{\mathrm{Span}},\qquad \sin(2\tau_{FP})=\frac{P_c}{m_{FP}\cdot\mathrm{Span}}.$$
--
--   These are eqs. (13) and (14) of the paper, which express the old degree of polarisation and the asymmetry factor through the old powers.
--
--   **Formalization Note** The hypothesis $m_{FP}>0$ is implicit in the paper, which divides by $m_{FP}\cdot\mathrm{Span}$ in eq. (14).
-- source:
--   J. D. Ballester-Berman, Analysing PolSAR data from vegetation by using the subaperture decomposition approach, arXiv:2405.02007v1 (2024), claim c024; Section 5.1, eqs. (2), (9), (13), (14), PDF pp. 2, 18-19

import Mathlib
import Definitions.Def_Arxiv2405_02007_Basic

open Real

namespace Arxiv2405_02007

theorem degree_and_asymmetry_from_powers (span m tau : ℝ) (hspan : 0 < span) (hm0 : 0 < m)
    (hm1 : m ≤ 1) :
    m = (span - volumePower m span) / span ∧
    Real.sin (2 * tau) = helixPower m span tau / (m * span) := by sorry

end Arxiv2405_02007

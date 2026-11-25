-- Prove2me | Theorems.Thm_Arxiv1408_1879_mean_plane_field_correction
-- name    : Arxiv1408_1879.mean_plane_field_correction
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T12:01:49.177088+00:00
-- url     : https://prove2.me/theorems/4aa7a6e4-da2c-4a66-8d4c-41884a4ec5f2
-- title:
--   Eq. (19): the mean-plane field is the standard PIE field plus h C
-- statement:
--   Let $\psi_i(x,z)$ be an incident field, $h$ a surface, and $\tilde\psi$, $C$ any two functions of $x$. Let $\Psi[u]$ be the mean-plane field of eq. (16), without its $O(\sigma^3)$ remainder, for a surface source $u=\partial\psi/\partial z$. Replacing the standard PIE source $\tilde\psi$ by the two-term truncation $\tilde\psi-C$ of series (12) gives
--   $$\Psi[\tilde\psi-C](x)=\tilde\psi_s(x,0)+h(x)C(x),\qquad\tilde\psi_s(x,0)=\Psi[\tilde\psi](x).$$
--   This is eq. (19), $\psi_s(x,0)=\tilde\psi_s(x,0)+h(x)C(x)$. With $\tilde\psi$ from eq. (17), $\tilde\psi_s$ is eq. (18).
--
--   **Formalization Note** The paper says it obtains (19) by "replacing (13) by (14)". With (14) as printed ($\tilde\psi+C$), eq. (16) gives $\tilde\psi_s-hC$. The printed $+hC$ follows from the truncation $\tilde\psi-C$ of series (12), which is what is stated here. The $O(\sigma^3)$ remainder of (16) is not part of the statement.
-- source:
--   M. Spivack and O. Rath Spivack, Rough surface backscatter and statistics via extended parabolic integral equation, arXiv:1408.1879v2 (2015), claim c007; Section 4.1, eqs. (16), (18), (19), PDF p. 8

import Mathlib
import Definitions.Def_Arxiv1408_1879_Basic

open MeasureTheory Filter Topology

namespace Arxiv1408_1879

theorem mean_plane_field_correction (ψi : ℝ → ℝ → ℂ) (h : ℝ → ℝ) (ψt C : ℝ → ℂ) (x : ℝ) :
    meanPlaneField ψi h (fun s => ψt s - C s) x = meanPlaneField ψi h ψt x + (h x : ℂ) * C x := by sorry

end Arxiv1408_1879

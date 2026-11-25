-- Prove2me | Theorems.Thm_Arxiv1510_02920_thin_boundary_diverges
-- name    : Arxiv1510_02920.thin_boundary_diverges
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T02:11:18.869661+00:00
-- url     : https://prove2.me/theorems/c8da703a-6500-40b2-9cc2-20e427d0b52b
-- title:
--   Eq. (8): the boundary region cannot be made arbitrarily thin
-- statement:
--   Let $c>0$, $\gamma>0$, $\Omega\ne0$ and real $\omega\ne0$, and let $\varepsilon_a$ be the permittivity (3) with $P$ from (4) and $f$ from (8) of width $a$. Then
--
--   $$|\varepsilon_a(0,\omega)|\to\infty\qquad\text{as }a\to0^+.$$
--
--   **Formalization Note** The paper says only that $a\to0$ "would give a diverging permittivity". The divergence is stated at the centre $x=0$ of the transition region. For fixed $x\ne0$ the permittivity stays bounded as $a\to0^+$.
-- source:
--   T. G. Philbin, All-frequency reflectionlessness, arXiv:1510.02920v1 (2015), claim c008; unnumbered main text, paragraph after Figure 1, PDF p. 4

import Mathlib
import Definitions.Def_Arxiv1510_02920_Basic

open Filter Topology Asymptotics

namespace Arxiv1510_02920

theorem thin_boundary_diverges (c γ Om ω : ℝ) (hc : 0 < c) (hγ : 0 < γ) (hOm : Om ≠ 0)
    (hω : ω ≠ 0) :
    Tendsto (fun a : ℝ => ‖tanhPerm c Om a γ 0 (ω : ℂ)‖) (𝓝[>] 0) atTop := by sorry

end Arxiv1510_02920

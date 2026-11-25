-- Prove2me | Theorems.Thm_Arxiv1506_07229_two_dimensional_limit_static_permittivity_positive
-- name    : Arxiv1506_07229.two_dimensional_limit_static_permittivity_positive
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T02:06:58.706078+00:00
-- url     : https://prove2.me/theorems/7e547d81-d503-4d26-abf2-882469f1647a
-- title:
--   Eq. (B10) at $\omega=0$: no negative static permittivity in the strictly-2D limit
-- statement:
--   Let $q>0$, $\eta>0$, $n_{2D}>0$, and let $\omega_p^2(a)\,a\to4\pi n_{2D}$ as $a\to0^+$. In the strictly-2D limit $a\to0^+$ of the Drude slab, the static permittivity tends to
--
--   $$\varepsilon(q,0)\longrightarrow1+\frac{2\pi n_{2D}\,q}{\eta^2}>0.$$
--
--   This value is the static value of the 2D-electron-gas permittivity (B10). So a negative static permittivity is impossible in the purely 2D limit, unlike the slab of finite thickness and the Q2D crystals. This is the precise content of the paper's contrast between quasi-2D and purely 2D systems.
--
--   **Formalization Note** The interpretive part of the conclusion, "fundamental differences of the screening", is not a mathematical statement and is not formalized. The finite-thickness slab's negative static permittivity is shown only in Fig. 11 and is not part of this statement.
-- source:
--   V. U. Nazarov, Negative static permittivity and violation of Kramers-Kronig relations in quasi-two-dimensional crystals, arXiv:1506.07229v3 (2015), claim c027; Conclusions, PDF p. 5; Appendix B, Eq. (B10), PDF p. 8

import Mathlib
import Definitions.Def_Arxiv1506_07229_Basic

open MeasureTheory Filter Topology Real ComplexConjugate

namespace Arxiv1506_07229

theorem two_dimensional_limit_static_permittivity_positive (n η q : ℝ) (hn : 0 < n)
    (hη : 0 < η) (hq : 0 < q) (wp2 : ℝ → ℝ)
    (hwp : Tendsto (fun a => wp2 a * a) (𝓝[>] 0) (𝓝 (4 * π * n))) :
    Tendsto (fun a => (slabInvEps (drudeEps (wp2 a) η 0) a q)⁻¹) (𝓝[>] 0)
        (𝓝 (((1 + 2 * π * n * q / η ^ 2 : ℝ)) : ℂ)) ∧
      twoDEGEps n η q 0 = ((1 + 2 * π * n * q / η ^ 2 : ℝ) : ℂ) ∧
      0 < 1 + 2 * π * n * q / η ^ 2 := by sorry

end Arxiv1506_07229

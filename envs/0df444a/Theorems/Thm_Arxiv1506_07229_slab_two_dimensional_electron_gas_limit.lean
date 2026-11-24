-- Prove2me | Theorems.Thm_Arxiv1506_07229_slab_two_dimensional_electron_gas_limit
-- name    : Arxiv1506_07229.slab_two_dimensional_electron_gas_limit
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:06:25.06907+00:00
-- url     : https://prove2.me/theorems/54fe098a-af8a-4e51-bbb0-ac60685f4c64
-- title:
--   Eq. (B10): the thin Drude slab tends to the 2D electron gas
-- statement:
--   Let $q>0$, $\eta>0$, $n_{2D}>0$ and $\omega\in\mathbb{R}$. Let the slab of Appendix B have the Drude constituent permittivity $\varepsilon(\omega)=1-\omega_p^2/(\omega+i\eta)^2$ (B9), where $\omega_p^2=\omega_p^2(a)$ depends on the thickness $a$ with $\omega_p^2a\to4\pi n_{2D}$ as $a\to0^+$. Then the slab permittivity $\varepsilon(q,\omega)$ of Eq. (B8) satisfies
--
--   $$\varepsilon(q,\omega)\longrightarrow1-\frac{2\pi n_{2D}\,q}{(\omega+i\eta)^2}\qquad(a\to0^+),$$
--
--   the long-wave permittivity of the 2D electron gas (Eq. (B10)).
--
--   **Formalization Note** The slab permittivity is the reciprocal of the right-hand side of (B8) with the coefficients (B4). The limit is taken along $a\to0^+$ for an arbitrary choice of $\omega_p^2(a)$ with $\omega_p^2(a)\,a\to4\pi n_{2D}$, which covers the paper's $\omega_p^2a=4\pi n_{3D}a\to4\pi n_{2D}$.
-- source:
--   V. U. Nazarov, Negative static permittivity and violation of Kramers-Kronig relations in quasi-two-dimensional crystals, arXiv:1506.07229v3 (2015), claim c021; Appendix B, Eqs. (B9)-(B10), PDF p. 7-8

import Mathlib
import Definitions.Def_Arxiv1506_07229_Basic

open MeasureTheory Filter Topology Real ComplexConjugate

namespace Arxiv1506_07229

theorem slab_two_dimensional_electron_gas_limit (n η q ω : ℝ) (hn : 0 < n) (hη : 0 < η)
    (hq : 0 < q) (wp2 : ℝ → ℝ)
    (hwp : Tendsto (fun a => wp2 a * a) (𝓝[>] 0) (𝓝 (4 * π * n))) :
    Tendsto (fun a => (slabInvEps (drudeEps (wp2 a) η ω) a q)⁻¹) (𝓝[>] 0)
      (𝓝 (twoDEGEps n η q ω)) := by sorry

end Arxiv1506_07229

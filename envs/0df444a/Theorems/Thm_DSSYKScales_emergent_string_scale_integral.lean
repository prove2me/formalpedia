-- Prove2me | Theorems.Thm_DSSYKScales_emergent_string_scale_integral
-- name    : DSSYKScales.emergent_string_scale_integral
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T01:55:59.481705+00:00
-- url     : https://prove2.me/theorems/4b6e138a-f6c1-4ab8-8f8d-0badfbc986f6
-- title:
--   Emergent string scale regulates the IR divergence: $\int_{\mathbb R}\operatorname{sech}^2(\mathcal J q t)\,dt=2/(\mathcal J q)$
-- statement:
--   Let $\mathcal J>0$ and $q>0$. Then
--   $$\int_{-\infty}^{\infty}\frac{dt}{\cosh^2(\mathcal J q\,t)}=\frac{2}{\mathcal J q}.$$
--
--   In Section 4 the melonic resummation replaces the constant, IR-divergent integrand of the vacuum diagram (3.11) by $1/\cosh^2(\mathcal J q\,|t_1-t_2|)$ (eq. (4.1)). This introduces the emergent string scale $L_s=1/(\mathcal J q)$ (eq. (4.2)). The divergent $\int dt$ becomes the finite quantity (4.3), which is of order $L_s$. The statement gives the exact constant.
--
--   **Formalization Note** The paper writes "$\sim 1/(\mathcal J q)$". The exact value is $2/(\mathcal J q)$. The integral is the Lebesgue (Bochner) integral over $\mathbb R$. In Lean a non-integrable function has integral $0$, so the statement also asserts the value $2/(\mathcal Jq)\neq0$, which rules out that reading.
-- source:
--   L. Susskind, "De Sitter Space, Double-Scaled SYK, and the Separation of Scales in the Semiclassical Limit", arXiv:2209.09999v1 [hep-th] (2022), https://arxiv.org/abs/2209.09999, Section 4 (The Emergent String Scale), pp. 22-23, eqs. (4.1)-(4.3)

import Mathlib
import Definitions.Def_DSSYKScales_defs

open Filter Topology

namespace DSSYKScales
theorem emergent_string_scale_integral (J q : ℝ) (hJ : 0 < J) (hq : 0 < q) :
    ∫ t : ℝ, 1 / Real.cosh (J * q * t) ^ 2 = 2 / (J * q) := by sorry
end DSSYKScales

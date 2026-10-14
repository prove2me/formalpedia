-- Prove2me | Theorems.Thm_Apery_inner_integrals
-- name    : Apery.inner_integrals
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T16:48:09.117108+00:00
-- url     : https://prove2.me/theorems/fb01be23-1d42-4dc9-a9f9-830f36ddd288
-- title:
--   Inner table integrals: $\sum_{i<125}\int_{t_i}^{t_{i+1}} g_{\mathrm{in},i}(x)/x^3\,dx = 322437603634266857629/7535670527041937280000$
-- statement:
--   The sum of the integrals of the 125 affine inner table pieces against $x^{-3}$,
--
--   $$\sum_{i<125}\int_{t_i}^{t_{i+1}} \frac{g_{\mathrm{in},i}(x)}{x^3}\,dx = \frac{322437603634266857629}{7535670527041937280000},$$
--
--   computed with the antiderivative $\int_a^b (Ax+B)/x^3\,dx = A(1/a - 1/b) + \frac{B}{2}(1/a^2 - 1/b^2)$. This is `inner_integrals` of `Apery/Growth/TableIntegrals.lean`, the numerical evaluation of the inner table used in the inner prime-sum estimate. **Formalization Note** `tIn`, `gIn` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/TableIntegrals.lean#L57-L63

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset intervalIntegral

namespace Apery

theorem inner_integrals :
    ∑ i ∈ range 125, ∫ x in tIn i..tIn (i + 1), gIn i x / x ^ 3 =
      322437603634266857629 / 7535670527041937280000 := by
  sorry

end Apery

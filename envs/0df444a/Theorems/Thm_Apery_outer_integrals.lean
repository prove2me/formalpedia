-- Prove2me | Theorems.Thm_Apery_outer_integrals
-- name    : Apery.outer_integrals
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T16:09:38.889489+00:00
-- url     : https://prove2.me/theorems/c85da29d-8d43-404f-9dbf-1e6aef12eac3
-- title:
--   Outer table integrals: $\sum_{i<13}\int_{t_i}^{t_{i+1}} g_{\mathrm{out},i}(x)/x^3\,dx = 129101/96000$
-- statement:
--   The sum of the integrals of the thirteen affine outer table pieces against $x^{-3}$,
--
--   $$\sum_{i<13}\int_{t_i}^{t_{i+1}} \frac{g_{\mathrm{out},i}(x)}{x^3}\,dx = \frac{129101}{96000},$$
--
--   computed with the antiderivative $\int_a^b (Ax+B)/x^3\,dx = A(1/a - 1/b) + \frac{B}{2}(1/a^2 - 1/b^2)$. This is `outer_integrals` of `Apery/Growth/TableIntegrals.lean`. **Formalization Note** `tOut`, `gOut` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/TableIntegrals.lean#L64-L69

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset

namespace Apery

theorem outer_integrals :
    ∑ i ∈ range 13, ∫ x in tOut i..tOut (i + 1), gOut i x / x ^ 3 = 129101 / 96000 := by
  sorry

end Apery

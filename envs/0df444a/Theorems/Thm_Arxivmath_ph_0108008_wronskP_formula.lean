-- Prove2me | Theorems.Thm_Arxivmath_ph_0108008_wronskP_formula
-- name    : Arxivmath_ph_0108008.wronskP_formula
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:35:29.5668+00:00
-- url     : https://prove2.me/theorems/bd6439b2-2fe2-5f7c-8228-a032486f453e
-- title:
--   Section 2: explicit formula for $p(r)=v_0(r)u_2'(r)-v_0'(r)u_2(r)$
-- statement:
--   Let $v_0(r)=-\cos r$, $u_2(r)=(3r^{-2}-1)\sin r-3r^{-1}\cos r$ and $p(r)=v_0(r)u_2'(r)-v_0'(r)u_2(r)$. Then for every $r>0$,
--   $$p(r)=1-\frac{3+3\cos^2 r}{r^2}+\frac{3\sin(2r)}{r^3}.$$
-- source:
--   A. G. Ramm, A counterexample to the uniqueness result of Cox and Thompson, arXiv:math-ph/0108008v1, claim c003; Section 2, definition of p(r) and the unnumbered formula after it, PDF p. 2

import Mathlib
import Definitions.Def_Arxivmath_ph_0108008_Basic

open MeasureTheory Filter Topology Real

namespace Arxivmath_ph_0108008

theorem wronskP_formula (r : ℝ) (hr : 0 < r) :
    wronskP r = 1 - (3 + 3 * Real.cos r ^ 2) / r ^ 2 + 3 * Real.sin (2 * r) / r ^ 3 := by sorry

end Arxivmath_ph_0108008

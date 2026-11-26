-- Prove2me | Theorems.Thm_Arxivmath_ph_0108008_wronskP_has_positive_zero
-- name    : Arxivmath_ph_0108008.wronskP_has_positive_zero
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T19:36:36.665319+00:00
-- url     : https://prove2.me/theorems/53907793-56b8-5ef6-a582-01742f8afab1
-- title:
--   Section 2, bold statement: there is $R>0$ with $p(R)=0$
-- statement:
--   There is a number $R>0$ with $p(R)=0$, where $p(r)=v_0(r)u_2'(r)-v_0'(r)u_2(r)$ is the function of Section 2.
--
--   **Formalization Note** The paper does not give the value of $R$. Numerically, the smallest positive zero is $R\approx2.44314$.
-- source:
--   A. G. Ramm, A counterexample to the uniqueness result of Cox and Thompson, arXiv:math-ph/0108008v1, claim c005; Section 2, bold statement 'There is a number R>0 such that p(R)=0', PDF p. 2

import Mathlib
import Definitions.Def_Arxivmath_ph_0108008_Basic

open MeasureTheory Filter Topology Real

namespace Arxivmath_ph_0108008

theorem wronskP_has_positive_zero : ∃ R : ℝ, 0 < R ∧ wronskP R = 0 := by sorry

end Arxivmath_ph_0108008

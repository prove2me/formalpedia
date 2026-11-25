-- Prove2me | Theorems.Thm_Arxivmath_ph_0108008_cox_thompson_uniqueness_fails
-- name    : Arxivmath_ph_0108008.cox_thompson_uniqueness_fails
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:34:26.464002+00:00
-- url     : https://prove2.me/theorems/3d0c1285-02ef-52bc-b8e4-07c8c02556fc
-- title:
--   Abstract and Section 1: the uniqueness claim of Cox and Thompson for Eq. (1.1) is false
-- statement:
--   Let $u_m$, $v_m$ be families of functions indexed by the order $m$, with $u_0(r)=\sin r$ and $v_0(r)=-\cos r$, for instance the regular and irregular Riccati–Bessel functions. Then the uniqueness claim of Cox and Thompson, as the paper restates it, is false. That is, there exist:
--   - finite disjoint sets $S,T$ of reals in $(-1/2,\infty)$;
--   - coefficients $\gamma_m$ satisfying $\sum_{m\in S}\gamma_m[m(m+1)-l(l+1)]^{-1}=1$ for all $l\in T$ (Eq. (1.2));
--   - a number $r>0$;
--   - a function $h$ that is continuous on $[0,r]$, has $h(0)=0$ and is not identically zero on $[0,r]$,
--
--   such that $h$ solves
--   $$h(s)=-\int_0^r g(s,t)\,h(t)\,t^{-2}\,dt,\qquad 0\le s\le r\qquad(1.1)$$
--   with $g(s,t)=\sum_{m\in S}\gamma_m u_m(\min(s,t))v_m(\max(s,t))$, the integral converging absolutely.
--
--   **Formalization Note** The paper's counterexample is $S=\{0\}$, $T=\{2\}$, $\gamma_0=-6$, $r=R$ a positive zero of $p$, and $h=u_2$. It uses only the order-$0$ functions. The statement therefore holds for every pair of families with $u_0=\sin$, $v_0=-\cos$, so the general Riccati–Bessel functions, which Mathlib lacks, need not be defined. The regularity required of a solution is a choice of this formalization; it makes the refutation stronger. The restatement allows $T=\emptyset$ and $|S|\ne|T|$, which the paper does not exclude; the witness has $|S|=|T|=1$, so it also refutes any version of the claim that requires $T\neq\emptyset$ or $|S|=|T|$. Whether this restatement matches the exact hypotheses of Cox and Thompson's paper cannot be decided from this paper.
-- source:
--   A. G. Ramm, A counterexample to the uniqueness result of Cox and Thompson, arXiv:math-ph/0108008v1, claim c001; Abstract and Section 1, Eqs. (1.1)-(1.2), PDF pp. 1-2

import Mathlib
import Definitions.Def_Arxivmath_ph_0108008_Basic

open MeasureTheory Filter Topology Real

namespace Arxivmath_ph_0108008

theorem cox_thompson_uniqueness_fails (u v : ℝ → ℝ → ℝ) (hu : u 0 = Real.sin)
    (hv : v 0 = fun r => -Real.cos r) :
    ¬ CoxThompsonClaim u v := by sorry

end Arxivmath_ph_0108008

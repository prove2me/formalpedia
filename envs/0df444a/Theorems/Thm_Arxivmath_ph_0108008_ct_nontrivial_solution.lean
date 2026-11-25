-- Prove2me | Theorems.Thm_Arxivmath_ph_0108008_ct_nontrivial_solution
-- name    : Arxivmath_ph_0108008.ct_nontrivial_solution
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:37:35.877932+00:00
-- url     : https://prove2.me/theorems/e5ac1c1a-b307-518d-8ead-7d0cc5091e29
-- title:
--   Section 2, Claim: for $r=R$ with $p(R)=0$, $u_2$ is a nontrivial solution of (1.1)
-- statement:
--   Let $u_m,v_m$ be families with $u_0=\sin$, $v_0=-\cos$. Take $S=\{0\}$, $T=\{2\}$ and $\gamma$ satisfying (1.2). Let $R>0$ with $p(R)=0$. Then $h=u_2$ solves Eq. (1.1) with upper limit $r=R$: it is continuous on $[0,R]$, $h(0)=0$, the integral converges absolutely, and
--   $$u_2(s)=-\int_0^R g(s,t)\,u_2(t)\,t^{-2}\,dt,\qquad 0\le s\le R .$$
--   Moreover $u_2$ is not identically zero on $(0,R)$. So for these $S$, $T$ and $r=R$, (1.1) has a nontrivial solution.
-- source:
--   A. G. Ramm, A counterexample to the uniqueness result of Cox and Thompson, arXiv:math-ph/0108008v1, claim c007; Section 2, Claim and the last line of its proof, PDF p. 2

import Mathlib
import Definitions.Def_Arxivmath_ph_0108008_Basic

open MeasureTheory Filter Topology Real

namespace Arxivmath_ph_0108008

theorem ct_nontrivial_solution (u v : ℝ → ℝ → ℝ) (hu : u 0 = Real.sin)
    (hv : v 0 = fun r => -Real.cos r) (γ : ℝ → ℝ) (hγ : CTCoeffEq {0} {2} γ)
    (R : ℝ) (hR : 0 < R) (hpR : wronskP R = 0) :
    IsCTSolution (ctKernel u v {0} γ) R riccatiU2 ∧ ∃ s ∈ Set.Ioo 0 R, riccatiU2 s ≠ 0 := by sorry

end Arxivmath_ph_0108008

-- Prove2me | Theorems.Thm_Arxiv1408_1879_two_way_reduces_to_one_way
-- name    : Arxiv1408_1879.two_way_reduces_to_one_way
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T11:36:15.597656+00:00
-- url     : https://prove2.me/theorems/36c8fb7b-e8ca-4af7-960a-d67d65e4b1cc
-- title:
--   Eq. (13): L is the standard PIE operator, and the two-way field adds the R-part
-- statement:
--   Let $k\in\mathbb{R}$, a surface $h$ and a surface source $f$ be given.
--
--   1. For $x'<x$, $G(x,z;x',z')=G_p(x,z;x',z')$. For $x'\ge x$, $G_p(x,z;x',z')=0$.
--   2. For $x\ge0$, the operator $L$ is the standard (one-way) PIE operator of eqs. (2) and (3):
--   $$Lf(x,z)=\int_0^xG_p\big((x,z),(x',h(x'))\big)f(x')\,dx'.$$
--   3. For $x\ge0$, if the integrand is integrable on $[0,x]$ and $\int_x^\infty$ converges, the two-way field (7) is the one-way field (3) plus the part $Rf$ from sources to the right:
--   $$\int_0^\infty G(r,r')f(x')\,dx'=\int_0^xG_p(r,r')f(x')\,dx'+Rf(x,z).$$
--
--   So the first term $L^{-1}\psi_i$ of (12) is the standard PIE solution for $\partial\psi/\partial z$, up to sign: under the convention of eq. (2), $\psi_i=-\int_0^xG_p\,\partial\psi/\partial z$, the PIE solution is $-L^{-1}\psi_i$ (the paper's (2) and (10) use opposite signs). This remark is not part of the formal statement, which proves only the operator identities above. Substituting it into (7) still gives the component $Rf$ scattered back towards the source, which the paper calls the direct backscatter.
-- source:
--   M. Spivack and O. Rath Spivack, Rough surface backscatter and statistics via extended parabolic integral equation, arXiv:1408.1879v2 (2015), claim c004; Section 3.2, eq. (13), with Section 2, eqs. (2), (3) and the display defining G_p, and eq. (6); PDF pp. 4-6

import Mathlib
import Definitions.Def_Arxiv1408_1879_Basic

open MeasureTheory Filter Topology

namespace Arxiv1408_1879

theorem two_way_reduces_to_one_way (k : ℝ) (h : ℝ → ℝ) (f : ℝ → ℂ) :
    (∀ x z x' z' : ℝ, x' < x → greenTwoWay k x z x' z' = greenOneWay k x z x' z') ∧
    (∀ x z x' z' : ℝ, x ≤ x' → greenOneWay k x z x' z' = 0) ∧
    (∀ x z : ℝ, 0 ≤ x →
      leftOp k h f x z = ∫ x' in (0 : ℝ)..x, greenOneWay k x z x' (h x') * f x') ∧
    (∀ x z : ℝ, 0 ≤ x →
      IntervalIntegrable (fun x' => greenTwoWay k x z x' (h x') * f x') volume 0 x →
      ImproperIntegrable (fun x' => greenTwoWay k x z x' (h x') * f x') x →
      twoWayField k h f x z =
        (∫ x' in (0 : ℝ)..x, greenOneWay k x z x' (h x') * f x') + rightOp k h f x z) := by sorry

end Arxiv1408_1879

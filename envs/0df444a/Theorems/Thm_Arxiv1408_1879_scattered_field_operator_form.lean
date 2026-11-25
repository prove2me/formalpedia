-- Prove2me | Theorems.Thm_Arxiv1408_1879_scattered_field_operator_form
-- name    : Arxiv1408_1879.scattered_field_operator_form
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T11:29:43.92072+00:00
-- url     : https://prove2.me/theorems/eaae8411-bb05-46fe-88c0-2c54f338b661
-- title:
--   Eqs. (7)-(9): the two-way scattered field in operator form (as proved)
-- statement:
--   Let $k\in\mathbb{R}$, let $h:\mathbb{R}\to\mathbb{R}$ be a surface, $f:\mathbb{R}\to\mathbb{C}$ a surface source, $x\ge0$ and $z\in\mathbb{R}$. Write $F(x')=G\big((x,z),(x',h(x'))\big)f(x')$.
--
--   1. If $F$ is integrable on $[0,x]$ and the improper integral $\int_x^\infty F$ converges, then $\int_0^\infty F$ converges and
--   $$\int_0^\infty G(r,r')f(x')\,dx'=Lf(x,z)+Rf(x,z).$$
--   Thus the scattered field (7) is $\psi_s=(L+R)\,\partial\psi/\partial z$.
--   2. ($L$ is one-sided.) If $g=f$ on $[0,x]$, then $Lg(x,z)=Lf(x,z)$.
--   3. ($R$ is one-sided.) If $g=f$ on $[x,\infty)$, then $Rg(x,z)=Rf(x,z)$.
--
--   These are the operator form of eq. (7) and the Volterra (one-sided) property of $L$ and $R$.
--
--   **Formalization Note** Eq. (9) is printed as $\psi_s=-(L+R)\,\partial\psi/\partial z$, the opposite sign to eq. (7). The statement follows eq. (7) and the definitions of $L$ and $R$ (as proved). The paper also asserts that $L^{-1}$ and $R^{-1}$ are Volterra "in an obvious sense". That assertion is not included, because the paper does not say on which function space the inverses act.
-- source:
--   M. Spivack and O. Rath Spivack, Rough surface backscatter and statistics via extended parabolic integral equation, arXiv:1408.1879v2 (2015), claim c002; Section 3.1, eqs. (7), (9) and the definition of L, R after eq. (10), PDF p. 5

import Mathlib
import Definitions.Def_Arxiv1408_1879_Basic

open MeasureTheory Filter Topology

namespace Arxiv1408_1879

theorem scattered_field_operator_form (k : ℝ) (h : ℝ → ℝ) (f : ℝ → ℂ) (x z : ℝ) (hx : 0 ≤ x) :
    (IntervalIntegrable (fun x' => greenTwoWay k x z x' (h x') * f x') volume 0 x →
      ImproperIntegrable (fun x' => greenTwoWay k x z x' (h x') * f x') x →
      ImproperIntegrable (fun x' => greenTwoWay k x z x' (h x') * f x') 0 ∧
        twoWayField k h f x z = leftOp k h f x z + rightOp k h f x z) ∧
    (∀ g : ℝ → ℂ, (∀ x' ∈ Set.Icc 0 x, g x' = f x') → leftOp k h g x z = leftOp k h f x z) ∧
    (∀ g : ℝ → ℂ, (∀ x' ∈ Set.Ici x, g x' = f x') → rightOp k h g x z = rightOp k h f x z) := by sorry

end Arxiv1408_1879

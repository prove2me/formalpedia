-- Prove2me | Theorems.Thm_DerivativeChainPrivate_rational_inverse_parts
-- name    : DerivativeChainPrivate.rational_inverse_parts
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T03:21:35.220998+00:00
-- url     : https://prove2.me/theorems/193bf614-42a4-43e0-a2ec-931550d26b68
-- title:
--   Real and imaginary parts of a rational inverse identity
-- statement:
--   Let $\beta,z\in\mathbb C$ and real $\alpha,b,d,c$ satisfy $z\ne0$, $z^2-c\ne0$, and $\beta/z=\alpha z^2-b+d/(z^2-c)$. Put $x=\operatorname{Re}z$, $y=\operatorname{Im}z$, $U=x^2+y^2$, $D=|z^2-c|^2$. Then
--
--   $$\operatorname{Re}\beta=x[\alpha(x^2-3y^2)-b+d(U-c)/D],$$\n$$\operatorname{Im}\beta=y[\alpha(3x^2-y^2)-b-d(U+c)/D],$$\n$$\operatorname{Im}(\beta/z)=2xy(\alpha-d/D),\qquad D=(U-c)^2+4cy^2.$$
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Dependencies/VerifiedCube.lean#L596-L634

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.rational_inverse_parts (β z : ℂ) (α b d c : ℝ)
    (hz : z ≠ 0) (hpole : z ^ 2 - (c : ℂ) ≠ 0)
    (hβ : β / z = (α : ℂ) * z ^ 2 - (b : ℂ) + (d : ℂ) / (z ^ 2 - (c : ℂ))) :
    let U := z.re ^ 2 + z.im ^ 2
    let D := ‖z ^ 2 - (c : ℂ)‖ ^ 2
    β.re = z.re * (α * (z.re ^ 2 - 3 * z.im ^ 2) - b + d * (U - c) / D) ∧
      β.im = z.im * (α * (3 * z.re ^ 2 - z.im ^ 2) - b - d * (U + c) / D) ∧
      (β / z).im = 2 * z.re * z.im * (α - d / D) ∧
      D = (U - c) ^ 2 + 4 * c * z.im ^ 2 := by sorry

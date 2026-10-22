-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_disk_near_side_force_negative
-- name    : BirkhoffGlobalSection.inner_lagrange_disk_near_side_force_negative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-25T06:45:09.399985+00:00
-- url     : https://prove2.me/theorems/0943917d-d699-4e13-a44f-df4089653521
-- title:
--   Horizontal force sign on the near half of the first Lagrange disk
-- statement:
--   On the half of the Lagrange disk facing the second primary, the horizontal force pulls back toward the first primary.
--
--   Fix $0<\mu<1$. The primary of mass $1-\mu$ sits at $(-\mu,0)$ and the primary of mass $\mu$ at $(1-\mu,0)$. The effective potential is $\Omega(x,y)=\tfrac12(x^2+y^2)+\frac{1-\mu}{r_1}+\frac{\mu}{r_2}$, where $r_1=\sqrt{(x+\mu)^2+y^2}$ and $r_2=\sqrt{(x-1+\mu)^2+y^2}$. Let $L$ be the inner collinear Lagrange point, and let $d=L_1+\mu$ be its distance from the first primary.
--
--   For every point $(x,y)$ with $x>-\mu$ and $r_1<d$,
--   $$
--   \partial_x\Omega(x,y)=x-\frac{(1-\mu)(x+\mu)}{r_1^3}-\frac{\mu(x-1+\mu)}{r_2^3}<0 .
--   $$
--
--   This is the sign of $\Omega_x$ on the side of the oval about the primary between the two primaries. There the zero curve of $\Omega_x$ does not enter, since in Birkhoff's analysis it lies on the far side. It yields the monotonicity $\tfrac{d}{dt}(\dot x+2y)=\Omega_x<0$ that keeps the horizontal velocity of the shooting family of one sign until the trajectory reaches the vertical line through the primary.
--
--   **Formalization Note** The statement is proved on the whole half-disk of radius $d$, which contains the corresponding half of the zero-velocity oval.
-- source:
--   G. D. Birkhoff, The restricted problem of three bodies, Rend. Circ. Mat. Palermo 39 (1915), Section 17 (signs of Omega_1 = Omega_x and Omega_2 = Omega_y in the oval of zero velocity about J), used in Section 18; Collected Mathematical Papers Vol. 1, pp. 734-737. Coordinates reflected x -> -x relative to Birkhoff.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem inner_lagrange_disk_near_side_force_negative (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (L : Phase) (hL : IsInnerLagrangePoint μ L)
    (x y : ℝ) (hx : -μ < x)
    (hr : (x + μ) ^ 2 + y ^ 2 < (L 0 + μ) ^ 2) :
    x - (1 - μ) * (x + μ) / Real.sqrt ((x + μ) ^ 2 + y ^ 2) ^ 3 -
      μ * (x - 1 + μ) / Real.sqrt ((x - 1 + μ) ^ 2 + y ^ 2) ^ 3 < 0 := by sorry

end BirkhoffGlobalSection

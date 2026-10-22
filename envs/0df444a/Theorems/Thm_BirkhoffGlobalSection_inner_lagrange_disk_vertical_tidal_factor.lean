-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_disk_vertical_tidal_factor
-- name    : BirkhoffGlobalSection.inner_lagrange_disk_vertical_tidal_factor
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-25T06:45:05.551982+00:00
-- url     : https://prove2.me/theorems/b66a69c8-f061-42f1-a820-ee28c2d59a30
-- title:
--   Vertical force sign inside the first Lagrange disk
-- statement:
--   Inside the disk reaching the first Lagrange point, the attraction of the two primaries dominates the vertical centrifugal force.
--
--   Fix $0<\mu<1$. The primary of mass $1-\mu$ sits at $(-\mu,0)$ and the primary of mass $\mu$ at $(1-\mu,0)$. The effective potential is $\Omega(x,y)=\tfrac12(x^2+y^2)+\frac{1-\mu}{r_1}+\frac{\mu}{r_2}$, where $r_1=\sqrt{(x+\mu)^2+y^2}$ and $r_2=\sqrt{(x-1+\mu)^2+y^2}$. Let $L$ be the inner collinear Lagrange point, and let $d=L_1+\mu$ be its distance from the first primary.
--
--   For every point $(x,y)\ne(-\mu,0)$ with $r_1<d$,
--   $$
--   \frac{1-\mu}{r_1^3}+\frac{\mu}{r_2^3}>1 .
--   $$
--
--   Equivalently, since $\partial_y\Omega=-y\bigl(\tfrac{1-\mu}{r_1^3}+\tfrac{\mu}{r_2^3}-1\bigr)$, the vertical force $\partial_y\Omega$ has the sign of $-y$ throughout this disk. This is the sign fact behind Birkhoff's observation that $\Omega_y$ vanishes in the oval about the primary only on the line of primaries and is negative on the side into which the orbit is launched. It forbids a trajectory with $\ddot y$ of the wrong sign at a horizontal tangency.
--
--   **Formalization Note** The statement is proved on the whole disk of radius $d$, which contains the zero-velocity oval around the first primary.
-- source:
--   G. D. Birkhoff, The restricted problem of three bodies, Rend. Circ. Mat. Palermo 39 (1915), Section 17 (signs of Omega_1 = Omega_x and Omega_2 = Omega_y in the oval of zero velocity about J), used in Section 18; Collected Mathematical Papers Vol. 1, pp. 734-737. Coordinates reflected x -> -x relative to Birkhoff.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

theorem inner_lagrange_disk_vertical_tidal_factor (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (L : Phase) (hL : IsInnerLagrangePoint μ L)
    (x y : ℝ) (hpos : 0 < (x + μ) ^ 2 + y ^ 2)
    (hr : (x + μ) ^ 2 + y ^ 2 < (L 0 + μ) ^ 2) :
    1 < (1 - μ) / Real.sqrt ((x + μ) ^ 2 + y ^ 2) ^ 3 +
      μ / Real.sqrt ((x - 1 + μ) ^ 2 + y ^ 2) ^ 3 := by sorry

end BirkhoffGlobalSection

-- Prove2me | Theorems.Thm_Arxivcond_mat_0107384_regular_polygon_radius
-- name    : Arxivcond_mat_0107384.regular_polygon_radius
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T20:15:52.429449+00:00
-- url     : https://prove2.me/theorems/98c8657a-5bb0-5d05-9b3c-44be5fb2c699
-- title:
--   Eq. (12): the radius of a regular $n$-gon of area $q$, and its limit $\sqrt{q/\pi}$ as $n\to\infty$
-- statement:
--   Let $0\le q\le1$ be the area fraction of the inclusion in a unit cell of area $1$. Let $c\in\mathbb{R}^2$ and $\theta\in\mathbb{R}$. For $n\ge3$ and $r\ge0$, let $P_n(r)$ be the closed regular $n$-gon with centre $c$, vertices at angles $\theta+2\pi k/n$, and circumradius $r$. Let $r_n=\sqrt{q/(n\sin(\pi/n)\cos(\pi/n))}$ (eq. 12) and $r=\sqrt{q/\pi}$. Then:
--
--   1. For every $n\ge3$ and $r\ge0$, $\operatorname{area}P_n(r)=n\,r^2\sin(\pi/n)\cos(\pi/n)$.
--   2. For every $n\ge3$ and $r\ge0$, $\operatorname{area}P_n(r)=q$ if and only if $r=r_n$. This is eq. (12).
--   3. $n\sin(\pi/n)\cos(\pi/n)\to\pi$ as $n\to\infty$.
--   4. $r_n\to\sqrt{q/\pi}$ as $n\to\infty$.
--   5. The polygon tends to the disk: the Hausdorff distance between $P_n(r_n)$ and the closed disk $\bar B(c,\sqrt{q/\pi})$ tends to $0$ as $n\to\infty$.
--
--   **Formalization Note** The paper says the polygon becomes a disk as $n\to\infty$ without naming a mode of convergence. Part 5 uses the Hausdorff distance. Both sets are nonempty and compact, so the distance is finite and meaningful. Areas are Lebesgue measures in $[0,\infty]$; part 1 is stated through `ENNReal.ofReal`, whose argument is nonnegative for $n\ge3$. The bound $q\le1$ is the paper's range of area fractions (Sec. 2); the mathematics does not use it. The claim record (c006, not the paper) notes that $q$ must be small enough for the polygon to fit in the cell; this only matters for the physical model and is not part of this statement.
-- source:
--   Tuncer, How round is round? On accuracy in complex dielectric permittivity calculations: a finite-size scaling approach, arXiv:cond-mat/0107384v3 (2002), claim c006; Sec. 4 (Results and discussion), eq. (12) and the sentences before and after it, PDF p. 8; disk radius r = sqrt(q/pi) from Sec. 2, after eqs. (6)-(7), PDF p. 4

import Mathlib
import Definitions.Def_Arxivcond_mat_0107384_Basic

open MeasureTheory Filter Topology

namespace Arxivcond_mat_0107384

theorem regular_polygon_radius (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (c : Plane) (θ : ℝ) :
    (∀ n : ℕ, 3 ≤ n → ∀ r : ℝ, 0 ≤ r →
      volume (regularPolygon n c r θ) =
        ENNReal.ofReal ((n : ℝ) * r ^ 2 * Real.sin (Real.pi / n) * Real.cos (Real.pi / n))) ∧
    (∀ n : ℕ, 3 ≤ n → ∀ r : ℝ, 0 ≤ r →
      (volume (regularPolygon n c r θ) = ENNReal.ofReal q ↔ r = polygonRadius n q)) ∧
    Tendsto (fun n : ℕ => (n : ℝ) * Real.sin (Real.pi / n) * Real.cos (Real.pi / n)) atTop
      (𝓝 Real.pi) ∧
    Tendsto (fun n : ℕ => polygonRadius n q) atTop (𝓝 (diskRadius q)) ∧
    Tendsto (fun n : ℕ => Metric.hausdorffEDist (regularPolygon n c (polygonRadius n q) θ)
      (Metric.closedBall c (diskRadius q))) atTop (𝓝 0) := by sorry

end Arxivcond_mat_0107384

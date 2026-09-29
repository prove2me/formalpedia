-- Prove2me | Theorems.Thm_CarrollGR_kruskal_coordinates
-- name    : CarrollGR.kruskal_coordinates
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T00:23:25.312402+00:00
-- url     : https://prove2.me/theorems/879c20b2-6d7b-4a5d-98a6-c4f5e3fd72a3
-- title:
--   Kruskal coordinates remove the singularity at $r=2Gm$
-- statement:
--   Let $G>0$, $m>0$ and consider the region $r>2Gm$ of the Schwarzschild geometry. Define Kruskal coordinates
--
--   $$u=\left(\frac{r}{2Gm}-1\right)^{1/2}e^{r/4Gm}\cosh\frac{t}{4Gm},\qquad v=\left(\frac{r}{2Gm}-1\right)^{1/2}e^{r/4Gm}\sinh\frac{t}{4Gm}.$$
--
--   Then, in the coordinates $(v,u,\theta,\phi)$, the Schwarzschild metric (72) takes the form
--
--   $$ds^2=\frac{32(Gm)^3}{r}e^{-r/2Gm}(-dv^2+du^2)+r^2(d\theta^2+\sin^2\theta\,d\phi^2),$$
--
--   where $r$ is related to $u,v$ by
--
--   $$u^2-v^2=e^{r/2Gm}\left(\frac{r}{2Gm}-1\right).$$
--
--   Since nothing in the Kruskal form blows up at $r=2Gm$, this shows the singularity of (72) there is a coordinate singularity.
--
--   **Formalization Note** "Takes the form" is encoded as the change-of-variables identity $J^{\mathsf T}K J=g_{\text{Schw}}$, with $J$ the Jacobian of $(t,r,\theta,\phi)\mapsto(v,u,\theta,\phi)$ and $K$ the Kruskal components evaluated at the same $r$ and $\theta$; the implicit relation (75) is stated as a separate conjunct.
-- source:
--   S. M. Carroll, "A No-Nonsense Introduction to General Relativity" (lecture notes, 2001), uploaded PDF, pp. 17–18, eqs. (73)–(75)

import Mathlib
import Definitions.Def_CarrollGR_Defs

open scoped ContDiff

namespace CarrollGR

theorem kruskal_coordinates (GN m : ℝ) (hGN : 0 < GN) (hm : 0 < m) (x : Coord)
    (hr : 2 * GN * m < x 1) :
    (jacobian (schwarzschildToKruskal GN m) x).transpose * kruskalMetricAt GN m (x 1) (x 2)
        * jacobian (schwarzschildToKruskal GN m) x = schwarzschild GN m x ∧
      kruskalU GN m (x 0) (x 1) ^ 2 - kruskalV GN m (x 0) (x 1) ^ 2
        = Real.exp (x 1 / (2 * GN * m)) * (x 1 / (2 * GN * m) - 1) := by sorry

end CarrollGR

-- Prove2me | Theorems.Thm_ConsistentSubmodular_fourThirds_boundary_edge
-- name    : ConsistentSubmodular.fourThirds_boundary_edge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:31.959579+00:00
-- url     : https://prove2.me/theorems/bd59cbd4-73c7-425b-89d1-356c27828097
-- title:
--   Four-thirds boundary — the formal credit-boundary edge is safe
-- statement:
--   For reals $p,d,q$ define
--   $$w = 2(1-d) - \frac{3(1-4d)}{q} - (p+d),\quad \delta = \frac{(3-q)w - (p+d) - 3d}{q},\quad o = 1 - d - \delta - w,$$
--   and for $z$ the boundary margin
--   $$\mu(p,d,q,z) = \tfrac14 - d - \delta z - o\,z(1-z).$$
--   Let $p,d,q,z$ be reals with $0 \le p \le \tfrac12$, $\tfrac p2 \le d < \tfrac14$, $d \le p(1-p)$, $q \ge \tfrac43$ and $0 \le z \le 1$. Then
--   $$0 \le \mu(p,d,q,z).$$
--   Thus the formal credit-boundary edge is safe for every parameter at least four thirds, including formal negative residual values on the boundary.
--
--   **Formalization Note** The quantities $w,\delta,o$ are the boundary values of the weight, the delta and the overlap; $o$ may be negative formally.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/FourThirdsBoundary.lean#L194-L253 (`ConsistentSubmodular.fourThirds_boundary_edge`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_FourThirdsBoundary

open ConsistentSubmodular

theorem ConsistentSubmodular.fourThirds_boundary_edge (p d q z : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (hdlow : p / 2 ≤ d) (hd4 : d < 1 / 4) (hcredit : d ≤ p * (1 - p))
    (hq : (4 : ℝ) / 3 ≤ q) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ fourThirdsBoundaryMargin p d q z := by sorry

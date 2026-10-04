-- Prove2me | Theorems.Thm_CelestialWedge_wedge_closure
-- name    : CelestialWedge.wedge_closure
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T02:33:50.00772+00:00
-- url     : https://prove2.me/theorems/86239f7f-e167-4568-8179-e79d4a830c63
-- title:
--   Eqs. (7.7)–(7.8): the wedge range is closed under the bracket
-- statement:
--   Let $(p,m)$ and $(q,n)$ be in the wedge range, i.e. $p+m-1,\ p-m-1,\ q+n-1,\ q-n-1\in\mathbb N$. If the structure constant of Eq. (7.8) is nonzero,
--   $$m(q-1)-n(p-1)\neq 0,$$
--   then $(p+q-2,\ m+n)$ is again in the wedge range: $p+q+m+n-3\in\mathbb N$ and $p+q-m-n-3\in\mathbb N$.
-- source:
--   Bin Zhu, Topics in Celestial holography: A bottom-up perspective, arXiv:2606.24285v3 [hep-th] (invited review for Physics Reports), https://arxiv.org/abs/2606.24285, Section 7.1, p. 40, Eqs. (7.7)–(7.8)

import Mathlib
import Definitions.Def_celestial_wedge_algebra

namespace CelestialWedge

theorem wedge_closure (p m q n : ℚ) (hpm : InWedge p m) (hqn : InWedge q n)
    (hc : structConst p m q n ≠ 0) : InWedge (p + q - 2) (m + n) := by sorry

end CelestialWedge

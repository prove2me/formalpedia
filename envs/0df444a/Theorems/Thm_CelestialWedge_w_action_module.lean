-- Prove2me | Theorems.Thm_CelestialWedge_w_action_module
-- name    : CelestialWedge.w_action_module
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T03:36:12.737436+00:00
-- url     : https://prove2.me/theorems/7da927db-78a1-477e-9ccc-dafd94d180fa
-- title:
--   Eq. (7.17): the gluon soft currents form a module for the $w_{1+\infty}$ wedge algebra
-- statement:
--   Let the wedge algebra act on the span $S$ of the gluon soft currents by Eq. (7.17),
--   $$w^p_m\cdot S^{q,a}_n=[m(q-1)-n(p-1)]\,S^{p+q-2,a}_{m+n},$$
--   extended bilinearly (with the right-hand side $0$ if $(p+q-2,m+n)$ leaves the wedge). This is a representation of the wedge algebra (7.8): for all $X,Y\in W$ and $s\in S$,
--   $$[X,Y]\cdot s=X\cdot(Y\cdot s)-Y\cdot(X\cdot s).$$
-- source:
--   Bin Zhu, Topics in Celestial holography: A bottom-up perspective, arXiv:2606.24285v3 [hep-th] (invited review for Physics Reports), https://arxiv.org/abs/2606.24285, Section 7.1, p. 41, Eq. (7.17)

import Mathlib
import Definitions.Def_celestial_wedge_algebra
import Definitions.Def_celestial_gluon_s_algebra

namespace CelestialWedge

open Complex

theorem w_action_module {ι : Type*} (X Y : WedgeSpace) (s : SSpace ι) :
    wAct (bracket X Y) s = wAct X (wAct Y s) - wAct Y (wAct X s) := by sorry

end CelestialWedge

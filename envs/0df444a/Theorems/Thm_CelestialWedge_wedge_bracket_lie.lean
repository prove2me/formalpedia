-- Prove2me | Theorems.Thm_CelestialWedge_wedge_bracket_lie
-- name    : CelestialWedge.wedge_bracket_lie
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T03:37:13.154577+00:00
-- url     : https://prove2.me/theorems/74b47e0d-df69-43a6-a77f-544f5bedeef4
-- title:
--   Eq. (7.8) defines a Lie algebra: the celestial $w_{1+\infty}$ wedge algebra
-- statement:
--   Let $W$ be the complex vector space with basis $\{w^p_m\}$, where $p\in\{1,\tfrac32,2,\dots\}$ and $1-p\le m\le p-1$ in integer steps. Equip it with the bilinear bracket of Eq. (7.8),
--   $$[w^p_m,w^q_n]=\bigl(m(q-1)-n(p-1)\bigr)\,w^{p+q-2}_{m+n}$$
--   (with the right-hand side read as $0$ if $(p+q-2,m+n)$ is outside the wedge). Then $W$ is a Lie algebra, the wedge algebra of $w_{1+\infty}$: for all $X,Y,Z\in W$,
--   $$[X,X]=0,\qquad [X,[Y,Z]]=[[X,Y],Z]+[Y,[X,Z]].$$
-- source:
--   Bin Zhu, Topics in Celestial holography: A bottom-up perspective, arXiv:2606.24285v3 [hep-th] (invited review for Physics Reports), https://arxiv.org/abs/2606.24285, Section 7.1, p. 40, Eqs. (7.6)–(7.8)

import Mathlib
import Definitions.Def_celestial_wedge_algebra

namespace CelestialWedge

theorem wedge_bracket_lie :
    (∀ X : WedgeSpace, bracket X X = 0) ∧
    (∀ X Y Z : WedgeSpace,
      bracket X (bracket Y Z) = bracket (bracket X Y) Z + bracket Y (bracket X Z)) := by sorry

end CelestialWedge

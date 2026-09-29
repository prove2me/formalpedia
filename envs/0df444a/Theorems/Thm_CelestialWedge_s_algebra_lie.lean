-- Prove2me | Theorems.Thm_CelestialWedge_s_algebra_lie
-- name    : CelestialWedge.s_algebra_lie
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T03:27:33.62207+00:00
-- url     : https://prove2.me/theorems/943bf12f-10d5-4fb2-8a78-a0da4c209d5b
-- title:
--   Eq. (7.16): the gluon soft $S$-algebra is a Lie algebra
-- statement:
--   Let $f^{ab}{}_c$ ($a,b,c$ in a finite colour set) be Lie-algebra structure constants: $f^{ab}{}_c=-f^{ba}{}_c$ and $\sum_d(f^{ab}{}_df^{dc}{}_e+f^{bc}{}_df^{da}{}_e+f^{ca}{}_df^{db}{}_e)=0$. Then the bracket of Eq. (7.16),
--   $$[S^{p,a}_m,S^{q,b}_n]=-i\sum_cf^{ab}{}_c\,S^{p+q-1,c}_{m+n},$$
--   extended bilinearly to the span $S$ of the $S^{q,a}_m$ ($(q,m)$ in the wedge range), is a Lie bracket: $[X,X]=0$ and $[X,[Y,Z]]=[[X,Y],Z]+[Y,[X,Z]]$ for all $X,Y,Z\in S$.
-- source:
--   Bin Zhu, Topics in Celestial holography: A bottom-up perspective, arXiv:2606.24285v3 [hep-th] (invited review for Physics Reports), https://arxiv.org/abs/2606.24285, Section 7.1, p. 41, Eqs. (7.15)–(7.16)

import Mathlib
import Definitions.Def_celestial_wedge_algebra
import Definitions.Def_celestial_gluon_s_algebra

namespace CelestialWedge

open Complex

theorem s_algebra_lie {ι : Type*} [Fintype ι] (f : ι → ι → ι → ℂ)
    (hf : IsLieStructureConstants f) :
    (∀ X : SSpace ι, sBracket f X X = 0) ∧
    (∀ X Y Z : SSpace ι,
      sBracket f X (sBracket f Y Z) =
        sBracket f (sBracket f X Y) Z + sBracket f Y (sBracket f X Z)) := by sorry

end CelestialWedge

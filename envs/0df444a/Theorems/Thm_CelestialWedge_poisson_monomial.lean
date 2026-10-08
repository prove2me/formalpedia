-- Prove2me | Theorems.Thm_CelestialWedge_poisson_monomial
-- name    : CelestialWedge.poisson_monomial
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T03:11:01.716144+00:00
-- url     : https://prove2.me/theorems/b35848c2-1693-4f3e-8319-34ecb96f3154
-- title:
--   Eq. (7.9): Poisson brackets of the monomials $u^{p+m-1}v^{p-m-1}$
-- statement:
--   For $(p,m)$ and $(q,n)$ in the wedge range, with $\{f,g\}=\partial_uf\,\partial_vg-\partial_vf\,\partial_ug$ on $\mathbb C[u,v]$,
--   $$\{u^{p+m-1}v^{p-m-1},\ u^{q+n-1}v^{q-n-1}\}=2\,[m(q-1)-n(p-1)]\;u^{(p+q-2)+(m+n)-1}\,v^{(p+q-2)-(m+n)-1}.$$
--   So the Poisson bracket reproduces Eq. (7.8) with overall factor exactly $2$. (If an exponent on the right would be $-1$, the coefficient vanishes; in the formal statement exponents are truncated at $0$.)
-- source:
--   Bin Zhu, Topics in Celestial holography: A bottom-up perspective, arXiv:2606.24285v3 [hep-th] (invited review for Physics Reports), https://arxiv.org/abs/2606.24285, Section 7.1, p. 40, Eq. (7.9)

import Mathlib
import Definitions.Def_celestial_wedge_algebra

namespace CelestialWedge

theorem poisson_monomial (p m q n : ℚ) (hpm : InWedge p m) (hqn : InWedge q n) :
    poisson (monomialOf p m) (monomialOf q n) =
      (2 * ((structConst p m q n : ℚ) : ℂ)) • monomialOf (p + q - 2) (m + n) := by sorry

end CelestialWedge

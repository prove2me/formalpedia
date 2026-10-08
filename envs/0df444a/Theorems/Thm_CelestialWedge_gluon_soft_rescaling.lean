-- Prove2me | Theorems.Thm_CelestialWedge_gluon_soft_rescaling
-- name    : CelestialWedge.gluon_soft_rescaling
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T03:17:42.989926+00:00
-- url     : https://prove2.me/theorems/b7ed0e64-b8d3-41bc-b69c-3083c995ec01
-- title:
--   Eqs. (7.14)–(7.16): rescaled soft gluon modes satisfy the $S$-algebra
-- statement:
--   Let $V$ be a complex vector space with a bilinear bracket, let $\iota$ be a finite set of colour indices with arbitrary complex constants $f^{ab}{}_c$, and let $R^{k,a}_n\in V$ be a family of vectors. Suppose Eq. (7.14) holds for all $(k,n)$, $(l,n')$ in the soft gluon range ($k$ an integer $\le 1$, $\tfrac{k-1}{2}\le n\le\tfrac{1-k}{2}$ in integer steps) and all colours $a,b$:
--   $$[R^{k,a}_n,R^{l,b}_{n'}]=\sum_c\Bigl(-if^{ab}{}_c\,\frac{(\frac{1-k}2-n+\frac{1-l}2-n')!}{(\frac{1-k}2-n)!(\frac{1-l}2-n')!}\frac{(\frac{1-k}2+n+\frac{1-l}2+n')!}{(\frac{1-k}2+n)!(\frac{1-l}2+n')!}\Bigr)R^{k+l-1,c}_{n+n'}.$$
--   Then the rescaled modes $S^{q,a}_m=(q-m-1)!(q+m-1)!\,R^{3-2q,a}_m$ of Eq. (7.15) satisfy Eq. (7.16) for all $(p,m)$, $(q,n)$ in the wedge range:
--   $$[S^{p,a}_m,S^{q,b}_n]=-i\sum_cf^{ab}{}_c\,S^{p+q-1,c}_{m+n}.$$
-- source:
--   Bin Zhu, Topics in Celestial holography: A bottom-up perspective, arXiv:2606.24285v3 [hep-th] (invited review for Physics Reports), https://arxiv.org/abs/2606.24285, Section 7.1, p. 41, Eqs. (7.14)–(7.16)

import Mathlib
import Definitions.Def_celestial_wedge_algebra
import Definitions.Def_celestial_gluon_s_algebra

namespace CelestialWedge

open Complex

theorem gluon_soft_rescaling {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Fintype ι]
    (br : V →ₗ[ℂ] V →ₗ[ℂ] V) (f : ι → ι → ι → ℂ) (R : ℚ → ι → ℚ → V)
    (hR : ∀ (k l n n' : ℚ) (a b : ι), InGluonSoftRange k n → InGluonSoftRange l n' →
      br (R k a n) (R l b n') =
        ∑ c, (-I * f a b c * gluonSoftCoeff k l n n') • R (k + l - 1) c (n + n'))
    (p q m n : ℚ) (a b : ι) (hpm : InWedge p m) (hqn : InWedge q n) :
    br (gluonRescale R p a m) (gluonRescale R q b n) =
      ∑ c, (-I * f a b c) • gluonRescale R (p + q - 1) c (m + n) := by sorry

end CelestialWedge

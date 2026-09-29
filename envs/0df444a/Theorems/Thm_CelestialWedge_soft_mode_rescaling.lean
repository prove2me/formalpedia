-- Prove2me | Theorems.Thm_CelestialWedge_soft_mode_rescaling
-- name    : CelestialWedge.soft_mode_rescaling
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T02:36:30.153163+00:00
-- url     : https://prove2.me/theorems/5a2b9797-f526-4ac0-889d-d17fe33b983a
-- title:
--   Eqs. (7.5)–(7.8): rescaled soft graviton modes satisfy the $w_{1+\infty}$ wedge algebra
-- statement:
--   Let $V$ be a complex vector space with a bilinear bracket $[\cdot,\cdot]$, let $\kappa\neq0$, and let $H^k_m\in V$ be a family of vectors (the conformally soft graviton modes). Suppose they satisfy Eq. (7.5): for all $(k,m)$, $(l,n)$ in the soft range ($k$ an integer $\le 2$, $\tfrac{k-2}{2}\le m\le\tfrac{2-k}{2}$ in integer steps),
--   $$[H^k_m,H^l_n]=-\frac\kappa2\,[n(2-k)-m(2-l)]\,\frac{\bigl(\tfrac{2-k}{2}-m+\tfrac{2-l}{2}-n-1\bigr)!\,\bigl(\tfrac{2-k}{2}+m+\tfrac{2-l}{2}+n-1\bigr)!}{\bigl(\tfrac{2-k}{2}-m\bigr)!\bigl(\tfrac{2-l}{2}-n\bigr)!\bigl(\tfrac{2-k}{2}+m\bigr)!\bigl(\tfrac{2-l}{2}+n\bigr)!}\,H^{k+l}_{m+n}.$$
--   Then the rescaled modes of Eq. (7.6), $w^p_m=\tfrac1\kappa(p-m-1)!(p+m-1)!\,H^{-2p+4}_m$, satisfy Eq. (7.8) for all $(p,m)$, $(q,n)$ in the wedge range:
--   $$[w^p_m,w^q_n]=[m(q-1)-n(p-1)]\,w^{p+q-2}_{m+n}.$$
-- source:
--   Bin Zhu, Topics in Celestial holography: A bottom-up perspective, arXiv:2606.24285v3 [hep-th] (invited review for Physics Reports), https://arxiv.org/abs/2606.24285, Section 7.1, pp. 39–40, Eqs. (7.5), (7.6), (7.8)

import Mathlib
import Definitions.Def_celestial_wedge_algebra

namespace CelestialWedge

theorem soft_mode_rescaling {V : Type*} [AddCommGroup V] [Module ℂ V]
    (br : V →ₗ[ℂ] V →ₗ[ℂ] V) (κ : ℂ) (hκ : κ ≠ 0) (H : ℚ → ℚ → V)
    (hH : ∀ k l m n : ℚ, InSoftRange k m → InSoftRange l n →
      br (H k m) (H l n) = softCoeff κ k l m n • H (k + l) (m + n))
    (p m q n : ℚ) (hpm : InWedge p m) (hqn : InWedge q n) :
    br (rescale κ H p m) (rescale κ H q n) =
      ((structConst p m q n : ℚ) : ℂ) • rescale κ H (p + q - 2) (m + n) := by sorry

end CelestialWedge

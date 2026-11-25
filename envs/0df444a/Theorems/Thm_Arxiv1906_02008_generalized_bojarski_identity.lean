-- Prove2me | Theorems.Thm_Arxiv1906_02008_generalized_bojarski_identity
-- name    : Arxiv1906_02008.generalized_bojarski_identity
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T15:00:46.600021+00:00
-- url     : https://prove2.me/theorems/67f0f162-4210-4931-b7b1-f5572870eee9
-- title:
--   Eq. (3.22): the generalized Bojarski identity for the Kirchhoff far field of a convex obstacle
-- statement:
--   Let $n\in\{2,3\}$ and let $D\subset\mathbb{R}^n$ be a convex, open, bounded, nonempty set with Lipschitz boundary and connected exterior, sound-soft ($\gamma_D=-2$) or sound-hard ($\gamma_D=2$), with outward unit normal $\nu$. For $\theta\in\mathbb{S}^{n-1}$ let $\partial D_-(\theta)=\{x\in\partial D:\ \nu(x)\cdot\theta<0\}$ and
--   $$K(\hat x,\theta,k)=\gamma_D\int_{\partial D_-(\theta)}\frac{\partial e^{ik\theta\cdot y}}{\partial\nu(y)}\,e^{-ik\hat x\cdot y}\,ds(y),$$
--   the right-hand side of the Kirchhoff approximation (3.21). Then for all $\hat x,\theta\in\mathbb{S}^{n-1}$ and all $k>k_->0$,
--   $$K(\hat x,\theta,k)+\overline{K(-\hat x,-\theta,k)}=-k^2\,\theta\cdot(\theta-\hat x)\,\gamma_D\int_{\mathbb{R}^n}\chi_D(y)e^{ik(\theta-\hat x)\cdot y}\,dy=U^\infty(\hat x,\theta,k).$$
--
--   **Formalization Note** The paper writes (3.22) with $u^\infty$ on the left and $\approx$ in the first step, the approximation being $u^\infty\approx K$ of (3.21). The statement is the exact part of the derivation: the identity for the Kirchhoff model $K$, obtained by combining the two illuminated integrals and applying the divergence theorem. The normal derivative is written out as $ik(\nu\cdot\theta)e^{ik\theta\cdot y}$.
-- source:
--   Xia Ji and Xiaodong Liu, Inverse acoustic scattering problems with multi-frequency sparse backscattering far field data, arXiv:1906.02008v2 (2019), claim c005; Section 3, eqs. (3.21)-(3.22), PDF p. 8

import Mathlib
import Definitions.Def_Arxiv1906_02008_Basic

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Arxiv1906_02008

theorem generalized_bojarski_identity {n : ℕ} (hn : n = 2 ∨ n = 3)
    (D : Set (Rn n)) (hD : IsScatteringDomain D) (hconv : Convex ℝ D) (soft : Bool)
    (xh θ : Rn n) (hxh : ‖xh‖ = 1) (hθ : ‖θ‖ = 1)
    (km : ℝ) (hkm : 0 < km) (k : ℝ) (hk : km < k) :
    kirchhoffFarField soft D xh θ k + starRingEnd ℂ (kirchhoffFarField soft D (-xh) (-θ) k) =
      kirchhoffU soft D xh θ k := by sorry

end Arxiv1906_02008

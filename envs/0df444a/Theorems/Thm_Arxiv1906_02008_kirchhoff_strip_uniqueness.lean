-- Prove2me | Theorems.Thm_Arxiv1906_02008_kirchhoff_strip_uniqueness
-- name    : Arxiv1906_02008.kirchhoff_strip_uniqueness
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T15:10:38.49983+00:00
-- url     : https://prove2.me/theorems/92ba7501-83dc-4861-94c1-ecc32f52a09a
-- title:
--   Theorem 3.3: the data $U^\infty$ at one pair of directions determine the strip $S_D(\phi)$
-- statement:
--   Let $n\in\{2,3\}$, $0<k_-<k^+$, $\hat x,\theta\in\mathbb{S}^{n-1}$ with $\hat x\ne\theta$, $\phi=(\theta-\hat x)/|\theta-\hat x|$, and fix the boundary type, sound-soft ($\gamma=-2$) or sound-hard ($\gamma=2$). Let $D_1,D_2\subset\mathbb{R}^n$ be convex, open, bounded, nonempty sets with Lipschitz boundary and connected exterior, and let
--   $$U_j^\infty(\hat x,\theta,k)=-k^2\,\theta\cdot(\theta-\hat x)\,\gamma\int_{\mathbb{R}^n}\chi_{D_j}(y)e^{ik(\theta-\hat x)\cdot y}\,dy .$$
--   If $U_1^\infty(\hat x,\theta,k)=U_2^\infty(\hat x,\theta,k)$ for all $k\in(k_-,k^+)$, then $S_{D_1}(\phi)=S_{D_2}(\phi)$.
--
--   **Formalization Note** "Uniquely determined" is stated as equality of the strips of two obstacles with equal data. Both obstacles have the same boundary type, as the paper's proof divides by the known $\gamma_D$. The convexity hypothesis is the standing assumption of the Kirchhoff part of Section 3 ("For a convex obstacle $D$", p. 7).
-- source:
--   Xia Ji and Xiaodong Liu, Inverse acoustic scattering problems with multi-frequency sparse backscattering far field data, arXiv:1906.02008v2 (2019), claim c006; Section 3, Theorem 3.3, eqs. (3.22)-(3.24), PDF p. 9

import Mathlib
import Definitions.Def_Arxiv1906_02008_Basic

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Arxiv1906_02008

theorem kirchhoff_strip_uniqueness {n : ℕ} (hn : n = 2 ∨ n = 3)
    (km kp : ℝ) (hkm : 0 < km) (hk : km < kp)
    (xh θ : Rn n) (hxh : ‖xh‖ = 1) (hθ : ‖θ‖ = 1) (hne : xh ≠ θ) (soft : Bool)
    (D₁ D₂ : Set (Rn n)) (h₁ : IsScatteringDomain D₁) (hc₁ : Convex ℝ D₁)
    (h₂ : IsScatteringDomain D₂) (hc₂ : Convex ℝ D₂)
    (hdata : ∀ k ∈ Ioo km kp, kirchhoffU soft D₁ xh θ k = kirchhoffU soft D₂ xh θ k) :
    strip D₁ (phiDir xh θ) = strip D₂ (phiDir xh θ) := by sorry

end Arxiv1906_02008

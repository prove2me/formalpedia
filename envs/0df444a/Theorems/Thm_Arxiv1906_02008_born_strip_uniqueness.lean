-- Prove2me | Theorems.Thm_Arxiv1906_02008_born_strip_uniqueness
-- name    : Arxiv1906_02008.born_strip_uniqueness
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T14:50:10.834285+00:00
-- url     : https://prove2.me/theorems/915fd8ce-b263-5b3f-ae35-15e04e82f465
-- title:
--   Theorem 3.2: Born far field data at one pair of directions determine the strip $S_D(\phi)$
-- statement:
--   Let $n\in\{2,3\}$, $0<k_-<k^+$, $\hat x,\theta\in\mathbb{S}^{n-1}$ with $\hat x\ne\theta$, and $\phi=(\theta-\hat x)/|\theta-\hat x|$. For $j=1,2$ let $D_j\subset\mathbb{R}^n$ be an open, bounded, nonempty set with Lipschitz boundary and connected exterior, and let $q_j>0$ be a refractive index with $q_j-1$ integrable and $\operatorname{supp}(q_j-1)=\overline{D_j}$. Assume that for $j=1,2$ the set
--   $$\{\alpha\in\mathbb{R}:\ \Pi_\alpha\subset S_{D_j}(\phi),\ \hat q_j(\alpha)=0\},\qquad \hat q_j(\alpha)=\int_{\Pi_\alpha}[q_j(y)-1]\,ds(y),$$
--   has Lebesgue measure zero. If the Born far fields $u_{B,j}^\infty(\hat x,\theta,k)=k^2\int_{\mathbb{R}^n}e^{ik(\theta-\hat x)\cdot y}[q_j(y)-1]\,dy$ agree for all $k\in(k_-,k^+)$, then $S_{D_1}(\phi)=S_{D_2}(\phi)$.
--
--   **Formalization Note** "Uniquely determined" is stated as equality of the strips of two media with equal data. The paper does not specify the regularity of $q$; integrability of $q-1$ is the minimal assumption under which the data (3.14) are defined. The smallness condition of the Born approximation is not a hypothesis of the theorem, which is about the data (3.14).
-- source:
--   Xia Ji and Xiaodong Liu, Inverse acoustic scattering problems with multi-frequency sparse backscattering far field data, arXiv:1906.02008v2 (2019), claim c003; Section 3, Theorem 3.2, eqs. (3.14)-(3.16), PDF pp. 6-7

import Mathlib
import Definitions.Def_Arxiv1906_02008_Basic

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Arxiv1906_02008

theorem born_strip_uniqueness {n : ℕ} (hn : n = 2 ∨ n = 3)
    (km kp : ℝ) (hkm : 0 < km) (hk : km < kp)
    (xh θ : Rn n) (hxh : ‖xh‖ = 1) (hθ : ‖θ‖ = 1) (hne : xh ≠ θ)
    (q₁ q₂ : Rn n → ℝ) (D₁ D₂ : Set (Rn n)) (h₁ : IsMedium q₁ D₁) (h₂ : IsMedium q₂ D₂)
    (hz₁ : volume {α : ℝ | hyperplane xh θ α ⊆ strip D₁ (phiDir xh θ) ∧ qhat q₁ xh θ α = 0} = 0)
    (hz₂ : volume {α : ℝ | hyperplane xh θ α ⊆ strip D₂ (phiDir xh θ) ∧ qhat q₂ xh θ α = 0} = 0)
    (hdata : ∀ k ∈ Ioo km kp, bornFarField q₁ xh θ k = bornFarField q₂ xh θ k) :
    strip D₁ (phiDir xh θ) = strip D₂ (phiDir xh θ) := by sorry

end Arxiv1906_02008

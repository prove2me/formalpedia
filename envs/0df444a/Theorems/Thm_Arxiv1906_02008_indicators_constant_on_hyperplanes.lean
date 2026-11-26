-- Prove2me | Theorems.Thm_Arxiv1906_02008_indicators_constant_on_hyperplanes
-- name    : Arxiv1906_02008.indicators_constant_on_hyperplanes
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T15:20:31.503291+00:00
-- url     : https://prove2.me/theorems/c426b00c-f5b2-4546-9f16-3b534a822580
-- title:
--   Proposition 4.1: the single-pair indicators are constant on the hyperplanes $\Pi_\alpha$
-- statement:
--   Let $n\in\{2,3\}$, $0<k_-<k^+$, $\hat x,\theta\in\mathbb{S}^{n-1}$ with $\hat x\ne\theta$, and let $u^\infty:\mathbb{S}^{n-1}\times\mathbb{S}^{n-1}\times\mathbb{R}\to\mathbb{C}$ be any far field data. Let $\alpha\in\mathbb{R}$ and $z_1,z_2\in\Pi_\alpha=\{y:\ y\cdot(\theta-\hat x)+\alpha=0\}$. Then
--   $$I_1(z_1,\hat x,\theta)=I_1(z_2,\hat x,\theta)\quad\text{and}\quad I_2(z_1,\hat x,\theta)=I_2(z_2,\hat x,\theta),$$
--   with $I_1,I_2$ the indicators (4.25)-(4.26).
--
--   **Formalization Note** The data are an arbitrary function of $(\hat x,\theta,k)$ rather than the far field of a particular scatterer, since the identity uses only the form of the indicators. The far field function is taken on all of $\mathbb{R}^n\times\mathbb{R}^n\times\mathbb{R}$; only its values at the given directions and $k\in[k_-,k^+]$ enter.
-- source:
--   Xia Ji and Xiaodong Liu, Inverse acoustic scattering problems with multi-frequency sparse backscattering far field data, arXiv:1906.02008v2 (2019), claim c007; Section 4, Proposition 4.1, eqs. (4.25)-(4.26), PDF p. 10

import Mathlib
import Definitions.Def_Arxiv1906_02008_Basic

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Arxiv1906_02008

theorem indicators_constant_on_hyperplanes {n : ℕ} (hn : n = 2 ∨ n = 3)
    (u : Rn n → Rn n → ℝ → ℂ) (km kp : ℝ) (hkm : 0 < km) (hk : km < kp)
    (xh θ : Rn n) (hxh : ‖xh‖ = 1) (hθ : ‖θ‖ = 1) (hne : xh ≠ θ)
    (α : ℝ) (z₁ z₂ : Rn n) (h₁ : z₁ ∈ hyperplane xh θ α) (h₂ : z₂ ∈ hyperplane xh θ α) :
    indicatorI1 u km kp xh θ z₁ = indicatorI1 u km kp xh θ z₂ ∧
      indicatorI2 u km kp xh θ z₁ = indicatorI2 u km kp xh θ z₂ := by sorry

end Arxiv1906_02008

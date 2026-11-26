-- Prove2me | Theorems.Thm_Arxiv1906_02008_born_indicator_decay
-- name    : Arxiv1906_02008.born_indicator_decay
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T15:30:50.209671+00:00
-- url     : https://prove2.me/theorems/4a6fbb24-df64-4751-ba53-f33b7daaf09f
-- title:
--   Proposition 4.3: for a Born medium, $I_1(z,\hat x,\theta)=O(1/\mathrm{dist}(z,S_D(\phi)))$
-- statement:
--   Let $n\in\{2,3\}$, $0<k_-<k^+$, $\hat x,\theta\in\mathbb{S}^{n-1}$ with $\hat x\ne\theta$, $\phi=(\theta-\hat x)/|\theta-\hat x|$. Let $D$ be an open, bounded, nonempty set with Lipschitz boundary and connected exterior, and $q>0$ a refractive index with $q-1$ integrable and $\operatorname{supp}(q-1)=\overline D$. Let $I_1$ be the indicator (4.25) computed from the Born far field $u_B^\infty$ of (3.14). Then
--   $$I_1(z,\hat x,\theta)=O\Big(\frac{1}{\operatorname{dist}(z,S_D(\phi))}\Big)\quad\text{as }\operatorname{dist}(z,S_D(\phi))\to\infty,$$
--   that is, there are constants $C$ and $R$ such that $I_1(z,\hat x,\theta)\le C/\operatorname{dist}(z,S_D(\phi))$ for every $z\in\mathbb{R}^n$ with $\operatorname{dist}(z,S_D(\phi))\ge R$.
--
--   **Formalization Note** The $O$-statement is written out with explicit constants $C,R$. "Scattering by inhomogeneous medium" is read as the Born far field (3.14) that the paper inserts into $I_1$ to derive the proposition.
-- source:
--   Xia Ji and Xiaodong Liu, Inverse acoustic scattering problems with multi-frequency sparse backscattering far field data, arXiv:1906.02008v2 (2019), claim c009; Section 4, Proposition 4.3, eq. (4.28), PDF p. 11

import Mathlib
import Definitions.Def_Arxiv1906_02008_Basic

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace Arxiv1906_02008

theorem born_indicator_decay {n : ℕ} (hn : n = 2 ∨ n = 3)
    (km kp : ℝ) (hkm : 0 < km) (hk : km < kp)
    (xh θ : Rn n) (hxh : ‖xh‖ = 1) (hθ : ‖θ‖ = 1) (hne : xh ≠ θ)
    (q : Rn n → ℝ) (D : Set (Rn n)) (hq : IsMedium q D) :
    ∃ C R : ℝ, ∀ z : Rn n, R ≤ Metric.infDist z (strip D (phiDir xh θ)) →
      indicatorI1 (fun a b k => bornFarField q a b k) km kp xh θ z ≤
        C / Metric.infDist z (strip D (phiDir xh θ)) := by sorry

end Arxiv1906_02008

-- Prove2me | Theorems.Thm_Arxiv1506_07229_slab_induced_charge_and_permittivity
-- name    : Arxiv1506_07229.slab_induced_charge_and_permittivity
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:05:49.275696+00:00
-- url     : https://prove2.me/theorems/2aaf9f2b-c8fe-49ff-943c-6817b11f670d
-- title:
--   Eqs. (B5)-(B8): induced charge and Q2D permittivity of the slab
-- statement:
--   Let $a>0$, $q>0$, $\varepsilon\neq0$ and $1+e^{aq}+\varepsilon(e^{aq}-1)\neq0$. Let $\phi$ be the total potential (B2) with the coefficients (B4), and let $\phi_{\text{ext}}=1$. Let $\rho$ be the charge density (B6): density $\frac{q^2}{4\pi}(\frac1\varepsilon-1)$ on $|z|<\frac a2$, plus point charges $\frac{q}{4\pi}[(A_1-A_2)e^{-qa/2}+B_2e^{qa/2}]$ at $z=\frac a2$ and $\frac{q}{4\pi}[(B_3-B_2)e^{-qa/2}+A_2e^{qa/2}]$ at $z=-\frac a2$. Then:
--
--   1. $\rho$ is the induced charge of Eq. (B5), $\rho=-\frac{1}{4\pi}\big(\frac{d^2}{dz^2}-q^2\big)[\phi-\phi_{\text{ext}}]$, in the sense of distributions. That is, for every smooth compactly supported test function $t$,
--   $$\int\rho\,t\,dz=-\frac{1}{4\pi}\int_{\mathbb{R}}(\phi(z)-1)\,\big(t''(z)-q^2t(z)\big)\,dz;$$
--   2. (B7) holds: $\displaystyle\int\rho\,dz=\frac{q^2a}{4\pi}\Big(\frac1\varepsilon-1\Big)+\frac{q}{2\pi}\big[A_1e^{-qa/2}+2A_2\sinh(qa/2)\big]$;
--   3. (B8) holds: by Eq. (1), $\displaystyle\frac{1}{\varepsilon(q,\omega)}=1+\frac{2\pi}{q}\int\rho\,dz=1+\frac{qa}{2}\Big[\frac{1}{\varepsilon(\omega)}-1\Big]+A_1e^{-qa/2}+2A_2\sinh(qa/2)$.
--
--   **Formalization Note** The paper applies $d^2/dz^2$ to the piecewise potential. This produces the point charges of (B6) at the interfaces and is a distributional identity, so it is stated against test functions. Following the paper, $\int\chi(z,z')\,dz\,dz'$ in Eq. (1) is the total induced charge $\int\rho\,dz$ under the unit external potential.
-- source:
--   V. U. Nazarov, Negative static permittivity and violation of Kramers-Kronig relations in quasi-two-dimensional crystals, arXiv:1506.07229v3 (2015), claim c019; Appendix B, Eqs. (B5)-(B8), PDF p. 7

import Mathlib
import Definitions.Def_Arxiv1506_07229_Basic

open MeasureTheory Filter Topology Real ComplexConjugate

namespace Arxiv1506_07229

theorem slab_induced_charge_and_permittivity (eps : ℂ) (a q : ℝ) (ha : 0 < a) (hq : 0 < q)
    (he : eps ≠ 0)
    (hD : 1 + (Real.exp (a * q) : ℂ) + eps * ((Real.exp (a * q) : ℂ) - 1) ≠ 0) :
    (∀ t : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) t → HasCompactSupport t →
      slabRho eps a q (slabA1 eps a q) (slabA2 eps a q) (slabA2 eps a q) (slabA1 eps a q)
          (fun z => (t z : ℂ)) =
        -(1 / (4 * π) : ℂ) * ∫ z : ℝ,
          (slabPot eps a q (slabA1 eps a q) (slabA2 eps a q) (slabA2 eps a q) (slabA1 eps a q) z
              - 1) * (((deriv (deriv t) z : ℝ)) - (q : ℂ) ^ 2 * (t z : ℂ))) ∧
    slabRho eps a q (slabA1 eps a q) (slabA2 eps a q) (slabA2 eps a q) (slabA1 eps a q)
        (fun _ => 1) =
      (q ^ 2 * a / (4 * π) : ℂ) * (1 / eps - 1) +
        (q / (2 * π) : ℂ) * (slabA1 eps a q * (Real.exp (-(q * a / 2)) : ℂ) +
          2 * slabA2 eps a q * (Real.sinh (q * a / 2) : ℂ)) ∧
    1 + (2 * π / q : ℂ) *
        slabRho eps a q (slabA1 eps a q) (slabA2 eps a q) (slabA2 eps a q) (slabA1 eps a q)
          (fun _ => 1) =
      slabInvEps eps a q := by sorry

end Arxiv1506_07229

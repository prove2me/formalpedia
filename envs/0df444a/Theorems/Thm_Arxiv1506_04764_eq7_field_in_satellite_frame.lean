-- Prove2me | Theorems.Thm_Arxiv1506_04764_eq7_field_in_satellite_frame
-- name    : Arxiv1506_04764.eq7_field_in_satellite_frame
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T14:08:25.264696+00:00
-- url     : https://prove2.me/theorems/c57afefb-0915-4cf0-9d52-a3ae419f3716
-- title:
--   Eq. (7): the far electric field in the satellite frame
-- statement:
--   Let $c,\epsilon_0,\mu_0>0$ with $\epsilon_0\mu_0c^2=1$, let $\beta\in\mathbb R^3$ with $|\beta|<1$, and let $\rho(r'',s)$, $j(r'',s)$ be charge and current densities, differentiable in time, such that for every $(r,t)$ the integrands of the far fields $E(r,t)$ and $B(r,t)$ of eqs. (3)-(4) are integrable over $r''\in\mathbb R^3$. Then the electric field in the frame moving with velocity $c\beta$, obtained from the Lorentz transformation (5), is, as a function of Earth-frame coordinates,
--
--   $$E'(r,t)=-\frac{\gamma\mu_0}{4\pi}\int\frac{d^3r''}{R}\Big[\partial_t(j-c\hat R\rho)+(\beta\cdot\partial_tj)\hat R-(\beta\cdot\hat R)\partial_tj-\frac{\gamma}{\gamma+1}\big(\beta\cdot\partial_t(j-c\hat R\rho)\big)\beta\Big],$$
--
--   with $\rho,j$ differentiated in time and then evaluated at $(r'',t-R/c)$, $R=|r-r''|$, $\hat R=(r-r'')/R$. Consequently, at the event $(r',t')$ of the satellite frame, $E'$ is given by the same expression with $r$ replaced everywhere (including in $\mathbf R$, $R$, $\hat R$) by $r'+\frac{\gamma-1}{\beta^2}(r'\cdot\beta)\beta+\gamma\beta ct'$ and with source time argument $\gamma(t'+\beta\cdot r'/c)-R/c$.
--
--   **Formalization Note** The relation $1/\epsilon_0=\mu_0c^2$, used implicitly to pass from (3)-(5) to (7), is a hypothesis. The integrability of the integrands of (3)-(4), implicit in the paper, is a hypothesis; it is what lets the Lorentz transformation pass inside the integral. The second part is stated by evaluating both sides at the Earth-frame coordinates (8)-(9) of $(r',t')$.
-- source:
--   Braun, Monjid, Rougé and Kerr, Generalization of the Van Cittert-Zernike theorem: observers moving with respect to sources, arXiv:1506.04764v1 (2015), claim c001; Sec. 2.1, eqs. (3)-(9) and the paragraph after eq. (9), PDF p. 5

import Mathlib
import Definitions.Def_Arxiv1506_04764_Basic

open MeasureTheory Complex

namespace Arxiv1506_04764

theorem eq7_field_in_satellite_frame (eps0 mu0 c : ℝ) (beta : V3)
    (rho : V3 → ℝ → ℝ) (j : V3 → ℝ → V3)
    (hc : 0 < c) (heps0 : 0 < eps0) (hmu0 : 0 < mu0) (hvac : eps0 * mu0 * c ^ 2 = 1)
    (hbeta : dotProduct beta beta < 1)
    (hrho : ∀ r'', Differentiable ℝ (rho r'')) (hj : ∀ r'', Differentiable ℝ (j r''))
    (hintE : ∀ r t, Integrable (farEIntegrand c rho j r t))
    (hintB : ∀ r t, Integrable (farBIntegrand c j r t)) :
    (∀ (r : V3) (t : ℝ),
      lorentzE c beta (farE eps0 c rho j r t) (farB mu0 c j r t) = eq7Field mu0 c beta rho j r t) ∧
    (∀ (r' : V3) (t' : ℝ),
      lorentzE c beta (farE eps0 c rho j (earthPos c beta r' t') (earthTime c beta r' t'))
          (farB mu0 c j (earthPos c beta r' t') (earthTime c beta r' t')) =
        eq7Field mu0 c beta rho j (earthPos c beta r' t') (earthTime c beta r' t')) := by sorry

end Arxiv1506_04764

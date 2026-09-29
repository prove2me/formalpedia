-- Prove2me | Theorems.Thm_BoltzmannBGK_bgk_H_theorem
-- name    : BoltzmannBGK.bgk_H_theorem
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T22:28:38.863304+00:00
-- url     : https://prove2.me/theorems/030d71f6-8944-4f6b-8e5b-8b2df6147dab
-- title:
--   BGK $H$-theorem: $\int(\log f)C[f]\le 0$, with equality iff $f=f^{(0)}$
-- statement:
--   Let $\tau>0$ and let $f$ be an admissible distribution function on velocity space: everywhere strictly positive, integrable, and with finite second velocity moment; assume in addition that the entropy-production integrand $v\mapsto(\log f(v))\,C[f](v)$ is integrable, where
--
--   $$C[f]=-\frac1\tau\big(f-f^{(0)}\big)$$
--
--   is the BGK collision operator and $f^{(0)}$ is the local Maxwellian of $f$, that is, the Maxwellian with the same density, bulk velocity and temperature as $f$. Then the entropy production is non-positive,
--
--   $$\int_{\mathbb R^3}\mathrm dv\,(\log f)\,C[f]\;\le\;0,$$
--
--   and it vanishes if and only if $f$ is equal to its own local Maxwellian almost everywhere:
--
--   $$\int_{\mathbb R^3}\mathrm dv\,(\log f)\,C[f]=0\iff f=f^{(0)}\ \text{a.e.}$$
--
--   This is part (b) of the source question in full, including the answer to "under what conditions does equality hold". It is the $H$-theorem for the BGK model: with $H=\int f\log f\,\mathrm dv$ the collision term contributes $\int(\log f)C[f]\,\mathrm dv$ to $\mathrm dH/\mathrm dt$, so collisions never decrease the entropy $-H$, and they leave it unchanged exactly on the local Maxwellians. Together with the conservation of $\rho$, $u$ and $\theta$, it is the structural reason why the BGK model relaxes to local thermodynamic equilibrium and reproduces the Euler equations in the hydrodynamic limit.
--
--   **Formalization Note** The integrability hypothesis on the entropy-production integrand is needed for the statement to have its intended content, because in Lean a non-integrable function integrates to $0$. The equality case is an almost-everywhere identity, which is the strongest conclusion available from the vanishing of the integral of a non-negative function.
-- source:
--   Oxford Honour School of Mathematical and Theoretical Physics Part C / MSc in Mathematical and Theoretical Physics, examination paper A15089W1, KINETIC THEORY, Hilary Term 2019 (Thursday 10 January 2019), Question 1, page 2. https://web.archive.org/web/20250913150648/https://mmathphys.physics.ox.ac.uk/sites/default/files/mmathphys/documents/media/kt_2019.pdf

import Definitions.Def_BoltzmannBGK_model

open MeasureTheory Real

namespace BoltzmannBGK

theorem bgk_H_theorem (τ : ℝ) (f : Vel → ℝ) (hτ : 0 < τ) (hf : IsKineticState f)
    (hint : Integrable fun v => Real.log (f v) * collision τ f v) :
    (∫ v, Real.log (f v) * collision τ f v ≤ 0) ∧
      ((∫ v, Real.log (f v) * collision τ f v = 0) ↔
        f =ᵐ[volume] localMaxwellian f) := by sorry

end BoltzmannBGK

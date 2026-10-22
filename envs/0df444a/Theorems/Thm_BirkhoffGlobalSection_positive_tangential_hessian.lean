-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_positive_tangential_hessian
-- name    : BirkhoffGlobalSection.positive_tangential_hessian
-- status  : Proved
-- author  : @Yivy Yu
-- created : 2026-09-12T15:10:43.425338+00:00
-- url     : https://prove2.me/theorems/71df5dd8-4d03-4013-ab07-926ea979cf51
-- title:
--   Proposition 4.4 — positive tangential Hessian
-- statement:
--   Let $0\leq\mu\leq1/2$ and $2.1\leq c\leq2.1+10^{-6}$. The Levi-Civita Hamiltonian is $C^2$ at every point of the selected energy component, and its tangential Hessian is positive definite: for every nonzero $v$ with $dK_{\mu,c}(s)[v]=0$,
--
--   $$
--   d\bigl(x\mapsto dK_{\mu,c}(x)[v]\bigr)(s)[v]>0.
--   $$
--
--   This is the positive-tangential-Hessian clause of Joung--van Koert, Proposition 4.4. The statement deliberately does not use this clause alone as the definition of a convex body. The cited computation uses CAPD 5.3.0 and the batch scripts in the public `soir/convexity` directory.
-- source:
--   Joung--van Koert, Proposition 4.4, https://arxiv.org/abs/2407.19159v3. The formal row asserts the positive-tangential-Hessian clause, not the proposition's separate Gauss--Kronecker-curvature conclusion.

import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

/-- Joung--van Koert, Proposition 4.4: the tangential Hessian is positive
definite throughout the validated parameter interval. -/
theorem positive_tangential_hessian (μ c : ℝ)
    (hμ0 : 0 ≤ μ) (hμhalf : μ ≤ 1 / 2)
    (hc0 : 21 / 10 ≤ c) (hc1 : c ≤ 21 / 10 + 1 / 1000000) :
    HasPositiveTangentialHessianOn
      (leviCivitaHamiltonian μ c) (leftEnergyComponent μ c) := by sorry

end BirkhoffGlobalSection

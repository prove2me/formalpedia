-- Prove2me | Theorems.Thm_CritWinSpin_rounded_euler_weak_budget
-- name    : CritWinSpin.rounded_euler_weak_budget
-- status  : Proved
-- author  : @Maxliu
-- created : 2026-11-17T18:23:32.521209+00:00
-- url     : https://prove2.me/theorems/970d5765-8903-430d-8f87-8f62d61ee165
-- title:
--   Theorem 4.4 — weak error of the finite rounded Euler trajectory
-- statement:
--   Consider the actual finite rounded Euler trajectory for the regularized Ising envelope potential $U_\alpha$, with the certified geometry and Gibbs moments. Let $R\ge2$ dominate the moments and satisfy $\alpha R\ge1$. Suppose the step scale and explicit drift, Gaussian-grid, and rounding errors satisfy
--
--   $$\sigma\le\frac1{2048R^4},\qquad e\le\frac{\sigma^2}{16R^3},\qquad T\ge\frac{16R^4}{\sigma^2}.$$
--
--   For every bounded measurable test function $f$ with Lipschitz constant $0\le L\le R$, the trajectory law $\nu_T$ started at zero satisfies
--
--   $$\left|\int f\,d\nu_T-\int f\,d\mu_{U_\alpha}\right|\le\frac1{2R}.$$
--
--   The error $e$ is the explicit expression in the statement for the finite rational drift, Gaussian draw, and rounding schedules. The trajectory law is defined by those numerical updates. This supplies the discretization estimate used by the sampler in Theorem 4.4.
-- source:
--   Liu–Zhang–Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), Section 4, pp.15–17, equations (23)–(24). Finite rounded-Euler implementation estimate for Theorem 4.4.

import Definitions.Def_CritWinSpin_SamplerNumericalData
set_option autoImplicit false
set_option linter.all false
noncomputable section
open MeasureTheory ProbabilityTheory CritWinSpin
open CritWinSpin.LocalTM2.Compiled CritWinSpin.Implementation
open EnvelopeGeometry LangevinBudget

namespace CritWinSpin

theorem rounded_euler_weak_budget {N : ℕ} (S : SpinLaw) (hS : IsGHS S) (D : EulerData N)
    (hs : tau S < (D.sCap:ℝ)) (ha : 0 < D.a) (ha1 : D.a ≤ 1)
    (hPSD : ((D.sCap:ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ) - castM D.L*(castM D.L).transpose).PosSemidef)
    (hd : 0 < D.dPhi) (hd1 : D.dPhi ≤ 1) (hsnap : 0 < D.snap)
    (hr : 0 < D.dRound) (hsigma : 0 < D.sigma) (B : ℝ) (hB : 0 ≤ B)
    (hL : ∀ i j, |(D.L i j:ℝ)| ≤ B)
    (cert : Certificate N (D.a:ℝ))
    (hUeq : cert.U = potential S D.sCap D.a (castM D.L) (castV D.h))
    (hGeq : cert.g = gradient S D.sCap D.a (castM D.L) (castV D.h))
    {R : ℝ} (hR : 2 ≤ R) (haR : 1 ≤ (D.a:ℝ)*R)
    (hsR : (D.sigma:ℝ) ≤ 1/(2048*R^4))
    (hError :
      (D.sigma:ℝ)^2 * (((N:ℝ)+1)*((N:ℝ)*B*
        (2*(Fintype.card {x:ℚ // x∈S.A}:ℝ)*(D.dPhi:ℝ)/(S.ρ 1:ℝ))+2*(D.snap:ℝ))) +
        (D.sigma:ℝ)*((N:ℝ)/((D.k:ℝ)+1))+((N:ℝ)+1)*(D.dRound:ℝ) ≤
      (D.sigma:ℝ)^2/(16*R^3))
    (hM : (∫ x, ‖x‖ ∂DensityAnalysis.gibbs cert.U) ≤ R)
    (hH : 2+(∫ x, ‖cert.g x‖^6 ∂DensityAnalysis.gibbs cert.U)+
      GaussianMoments.sixthConstant*(N:ℝ)^3 ≤ R)
    (T : ℕ) (hT : 16*R^4/(D.sigma:ℝ)^2 ≤ (T:ℝ))
    (f : DensityAnalysis.Point N → ℝ) (Bf L : ℝ) (hLip : 0 ≤ L) (hLR : L ≤ R) (hf : Measurable f) (hfB : ∀ x, |f x| ≤ Bf)
    (hfL : ∀ x y, |f x-f y| ≤ L*dist x y) :
    |(∫ x, f x ∂D.trajectoryLaw S T (0 : Fin N → ℚ))-
      ∫ x, f x ∂DensityAnalysis.gibbs (potential S D.sCap D.a (castM D.L) (castV D.h))| ≤ 1/(2*R) := by sorry

end CritWinSpin

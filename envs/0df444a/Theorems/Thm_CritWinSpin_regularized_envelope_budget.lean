-- Prove2me | Theorems.Thm_CritWinSpin_regularized_envelope_budget
-- name    : CritWinSpin.regularized_envelope_budget
-- status  : Proved
-- author  : @Maxliu
-- created : 2026-11-17T18:12:38.375213+00:00
-- url     : https://prove2.me/theorems/24f22ebe-0258-4e9d-a138-bbda2ee740e0
-- title:
--   Theorem 4.4 — regularized envelope geometry and moment budget
-- statement:
--   Let $S$ be a GHS spin law and let $L$ satisfy $LL^\top\preceq sI$ with $s>\tau_S$. Assume the stated integrability and second-moment bounds for the envelope potential $W$. Choose a scale $C$ controlling the moment and kernel constants and put
--
--   $$B=C(N+1)(t+1),\qquad \alpha=B^{-1},\qquad R=B^{100}.$$
--
--   The regularized potential $U_\alpha$ has the analytic certificate needed by the finite Langevin sampler. Its Gibbs measure satisfies
--
--   $$\int\|x\|\,d\mu_{U_\alpha}\le R,\qquad 2+\int\|\nabla U_\alpha(x)\|^6\,d\mu_{U_\alpha}+c_6N^3\le R.$$
--
--   The same budget controls the kernel Lipschitz constant and the regularization error:
--
--   $$2C_k\sqrt N\le R,\qquad \frac1{4R}+\frac{\alpha M_0N}{2}\le\frac1{2048(t+1)}.$$
--
--   This isolates the geometry and moment estimates used in the proof of Theorem 4.4.
-- source:
--   Liu–Zhang–Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), Section 4, pp.14–17, equations (23)–(24). Quantitative regularization and moment estimates for the finite sampler in Theorem 4.4.

import Definitions.Def_CritWinSpin_SamplerAnalyticData
set_option autoImplicit false
set_option linter.all false
noncomputable section
open MeasureTheory CritWinSpin
open CritWinSpin.Implementation
open DensityAnalysis EnvelopeGeometry LangevinBudget

namespace CritWinSpin

theorem regularized_envelope_budget {N : ℕ} (S : SpinLaw) (hS : IsGHS S) {s C M₀ Cₖ t : ℝ}
    (L : Matrix (Fin N) (Fin N) ℝ) (h : Fin N → ℝ)
    (hs : tau S < s) (hsC : s ≤ C) (ht : 0 ≤ t)
    (hC : 131072 ≤ C) (hM₀ : 0 ≤ M₀) (hMC : 2048 * M₀ ≤ C)
    (hCₖ : 0 ≤ Cₖ) (hKC : 2 * Cₖ ≤ C) (hGC : GaussianMoments.sixthConstant ≤ C)
    (hPSD : (s • (1 : Matrix (Fin N) (Fin N) ℝ) - L * L.transpose).PosSemidef)
    (hiW : Integrable (fun z : Fin N → ℝ => Real.exp (-Wpot S s L h z)))
    (hiW2 : Integrable (fun z : Fin N → ℝ => normSq z * Real.exp (-Wpot S s L h z)))
    (hiU : Integrable (fun z : Fin N → ℝ => Real.exp (-Ualpha S s (1 / (C * ((N : ℝ) + 1) * (t + 1))) L h z)))
    (hMom : (∫ z : Fin N → ℝ, normSq z * normDens (Wpot S s L h) z) ≤ M₀ * (N : ℝ)) :
    let B := (C * ((N : ℝ) + 1) * (t + 1))
    ∃ cert : Certificate N (1 / B),
      cert.U = potential S s (1 / B) L h ∧ cert.g = gradient S s (1 / B) L h ∧
      0 < 1 / B ∧ 1 / B ≤ 1 ∧ 2 ≤ B ^ 100 ∧ 1 ≤ (1 / B) * B ^ 100 ∧
      (∫ x, ‖x‖ ∂DensityAnalysis.gibbs cert.U) ≤ B ^ 100 ∧
      2 + (∫ x, ‖cert.g x‖ ^ 6 ∂DensityAnalysis.gibbs cert.U) +
        GaussianMoments.sixthConstant * (N : ℝ) ^ 3 ≤ B ^ 100 ∧
      2 * (Cₖ * Real.sqrt (N : ℝ)) ≤ B ^ 100 ∧
      1 / (4 * B ^ 100) + (1 / B) * M₀ * (N : ℝ) / 2 ≤ 1 / (2048 * (t + 1)) := by sorry

end CritWinSpin

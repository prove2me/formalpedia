-- Prove2me | Theorems.Thm_CritWinSpin_numeric_kernel_trajectory_tv
-- name    : CritWinSpin.numeric_kernel_trajectory_tv
-- status  : Proved
-- author  : @Maxliu
-- created : 2026-11-17T18:28:28.926205+00:00
-- url     : https://prove2.me/theorems/86663607-85db-4786-99b1-593a49bb10dd
-- title:
--   Theorem 4.4 — finite sampling-kernel error along the Euler trajectory
-- statement:
--   Fix the finite numerical Euler data $D$ and a number of steps $T$. Let $\nu_T$ be its actual rounded trajectory law and let $r$ be the output law obtained by averaging the finite acceptance and spin draws over the trajectory's random-bit blocks.
--
--   Under the stated fuel, decoding, and kernel assumptions, its distance from the ideal kernel mixture satisfies
--
--   $$\operatorname{TV}\!\left(r,\int K(z,\cdot)\,\nu_T(dz)\right)\le\varepsilon_{\mathrm{num}}(S,C,N,k,s).$$
--
--   The explicitly defined error budget contains the integral discretization error and the finite-bit errors of the Bernoulli acceptance draw and the coordinate spin draws. This is the finite-kernel approximation component of the sampler in Theorem 4.4.
-- source:
--   Liu–Zhang–Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), Section 4, pp.15–17, equations (23)–(24). Finite acceptance/spin-kernel implementation estimate for Theorem 4.4.

import Definitions.Def_CritWinSpin_SamplerNumericalData
set_option autoImplicit false
set_option linter.all false
noncomputable section
open Classical IsingLTL.BeliefProp MeasureTheory CritWinSpin
open CritWinSpin.LocalTM2 CritWinSpin.LocalTM2.Compiled CritWinSpin.Implementation

theorem CritWinSpin.numeric_kernel_trajectory_tv {N : ℕ} (S : SpinLaw) (hS : IsGHS S) (C : ℕ) (hC : 0<C)
    (D : EulerData N) (T : ℕ) (hs : tau S < (D.sCap:ℝ))
    (hfSpin : 2 / (spinPrecision C D.k:ℝ)^3+2 ≤ D.fuel.length)
    (hTake : D.k+1 ≤ D.fuel.length)
    (hfIntegral : 2 / (1/((D.k:ℝ)+1))^3+2 ≤ (D.fuel.length:ℝ))
    (hnil : decConfig S N [] = none)
    (r : Option (Config S (Fin N)) → ℝ)
    (hmean : ∀ y, r y = FiniteDraw.mean (fun w : Fin T → Fin (N*gaussianNoiseBits D.k) → Bool =>
      kernelWordLaw S C D (finitePath (D.next S) (fun _ => 0) w) y))
    (Ck : ℝ) (hCk : 0 ≤ Ck)
    (hLip : ∀ z w : Fin N → ℝ,
      tvDist (kernelK S (D.sCap:ℝ) (castM D.L) (castV D.h) z)
        (kernelK S (D.sCap:ℝ) (castM D.L) (castV D.h) w) ≤
          Ck * Real.sqrt (N:ℝ) * Real.sqrt (normSq (z-w))) :
    tvDist r
      (fun x => ∫ z, SpinKernel.pointKernel S (D.sCap:ℝ) (castM D.L) (castV D.h) z x
        ∂D.trajectoryLaw S T (fun _ => 0)) ≤
      KernelPrecisionBudget.error S C N D.k (D.sCap:ℝ) := by sorry

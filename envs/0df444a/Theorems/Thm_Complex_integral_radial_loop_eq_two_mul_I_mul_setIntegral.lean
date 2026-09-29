-- Prove2me | Theorems.Thm_Complex_integral_radial_loop_eq_two_mul_I_mul_setIntegral
-- name    : Complex.integral_radial_loop_eq_two_mul_I_mul_setIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/4007561d-11da-5f1d-89cf-d89e18cd1fc7
-- title:
--   Green–Pompeiu formula on a radially parametrised region
-- statement:
--   Fix a centre $c \in \mathbb{C}$ and a radius function $r : \mathbb{R} \to \mathbb{R}$ which is continuous, periodic with period $2\pi$, and strictly positive at every angle. Suppose given $N \in \mathbb{N}$ and angles $\varphi_0 < \varphi_1 < \dots < \varphi_N$ (a strictly monotone family indexed by `Fin (N+1)`) with $\varphi_0 = 0$ and $\varphi_N = 2\pi$, such that $r$ is twice continuously differentiable on each closed subinterval $[\varphi_i, \varphi_{i+1}]$. Let $P, Q : \mathbb{C} \to \mathbb{C}$ and let $U \subseteq \mathbb{C}$ be open with the property that every $z$ satisfying $\|z - c\| \le r(\arg(z-c))$ lies in $U$; assume $P$ and $Q$ are continuously differentiable (as maps of the underlying real vector space) on $U$. Write $K = \{z : \|z-c\| \le r(\arg(z-c))\}$ and $\gamma(\varphi) = c + r(\varphi)e^{i\varphi}$, so that $\gamma'(\varphi) = (r'(\varphi) + i\,r(\varphi))e^{i\varphi}$. The conclusion is the identity $$\int_0^{2\pi}\Bigl(P(\gamma(\varphi))\,\gamma'(\varphi) + Q(\gamma(\varphi))\,\overline{\gamma'(\varphi)}\Bigr)\,d\varphi = 2i \int_K \left(\frac{D P_z(1) + i\,DP_z(i)}{2} - \frac{DQ_z(1) - i\,DQ_z(i)}{2}\right) dA(z),$$ the left side an interval integral in $\varphi$ and the right side an integral over $K$ against Lebesgue measure on $\mathbb{C}$, the integrand being $\partial_{\bar z}P - \partial_z Q$ expressed through the real Fréchet derivatives of $P$ and $Q$ evaluated at $1$ and at $i$.
--
--   This is Green's theorem in complex (Wirtinger) notation for the complex $1$-form $P\,dz + Q\,d\bar z$ on the compact region $K$ bounded by the radial loop $\varphi \mapsto c + r(\varphi)e^{i\varphi}$, giving $\oint_{\partial K} \beta = \int\int_K d\beta$ with $dz \wedge d\bar z = -2i\,dA$. It serves as the analytic input for [`Complex.integral_radial_loop_eq_two_pi_I_mul_sum_residue`](thm.html#Complex.integral_radial_loop_eq_two_pi_I_mul_sum_residue), the residue theorem for loops of this radial shape.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_integral_radial_loop_eq_two_mul_I_mul_setIntegral.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Complex in

theorem Complex.integral_radial_loop_eq_two_mul_I_mul_setIntegral
    (c : ℂ) (r : ℝ → ℝ) (hcont : Continuous r) (hper : Function.Periodic r (2 * Real.pi))
    (hpos : ∀ φ, 0 < r φ)
    (N : ℕ) (φs : Fin (N + 1) → ℝ) (hφ0 : φs 0 = 0) (hφN : φs (Fin.last N) = 2 * Real.pi)
    (hmono : StrictMono φs)
    (hC2 : ∀ i : Fin N, ContDiffOn ℝ 2 r (Set.Icc (φs i.castSucc) (φs i.succ)))
    (P Q : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hKU : ∀ z : ℂ, ‖z - c‖ ≤ r (arg (z - c)) → z ∈ U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi),
        (P (c + r φ * exp (φ * I)) * ((((deriv r φ : ℝ) : ℂ) + r φ * I) * exp (φ * I)) +
          Q (c + r φ * exp (φ * I)) *
            (starRingEnd ℂ) ((((deriv r φ : ℝ) : ℂ) + r φ * I) * exp (φ * I))) =
      2 * I * ∫ z in {z : ℂ | ‖z - c‖ ≤ r (arg (z - c))},
        ((fderiv ℝ P z 1 + I * fderiv ℝ P z I) / 2 - (fderiv ℝ Q z 1 - I * fderiv ℝ Q z I) / 2) := by sorry

-- Prove2me | Theorems.Thm_CarlssonPartition_Equitable_district_ratio
-- name    : CarlssonPartition.Equitable.district_ratio
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-16T06:17:15.585031+00:00
-- url     : https://prove2.me/theorems/649b7230-bcdb-42e3-baca-83e3c556305d
-- title:
--   Proof of Theorem 6, p. ec6 — each district's delivery time satisfies T_i/T(π*) → 1 in heavy traffic
-- statement:
--   Let the instance satisfy the standing assumptions with capacity $q\ge 2$, and let $\{\mathscr R_1,\dots,\mathscr R_m\}$ be a partition of $\mathscr R$ satisfying, for every $i$, the two equitable conditions
--   $$\iint_{\mathscr R_i}\sqrt{f(x)}\,dx=\frac1m\iint_{\mathscr R}\sqrt{f(x)}\,dx,\qquad \iint_{\mathscr R_i}(\bar svq+2\|x-x_0\|)f(x)\,dx=\frac1m\iint_{\mathscr R}(\bar svq+2\|x-x_0\|)f(x)\,dx.$$
--   Let $T(\pi^*)$ and $T_1,\dots,T_m$ be functions of the arrival rate $\lambda$ that obey Theorem 3 (Bertsimas and van Ryzin):
--   1. $T(\pi^*)(\lambda)/L_m(\lambda;\mathscr R,f)\to1$ as the fleet's workload factor $\rho+2\lambda\iint_{\mathscr R}\|x-x_0\|f/mvq$ tends to $1$ from below;
--   2. for each $i$, $T_i(\lambda)/L_1(\lambda_i;\mathscr R_i,f_i)\to1$ as district $i$'s own workload factor tends to $1$ from below, where $\lambda_i=\lambda\iint_{\mathscr R_i}f$ and $f_i=f/\iint_{\mathscr R_i}f$.
--
--   Here $L_k$ is Theorem 3's leading-order delivery time defined in the mission's `Setting`. Then for every district $i$,
--   $$\frac{T_i(\lambda)}{T(\pi^*)(\lambda)}\to1\qquad\text{in heavy traffic, i.e. as }\rho+\frac{2\lambda\iint_{\mathscr R}\|x-x_0\|f(x)\,dx}{mvq}\to1^-.$$
--
--   This is the per-district half of Theorem 6: the expected delivery time is asymptotically the same in every district, and the same as that of the flexible policy $\pi^*$.
--
--   **Formalization Note.** The delivery times are arbitrary real functions of $\lambda$ constrained only by Theorem 3 as hypotheses (the stochastic model is not formalized). The page also says the policy is asymptotically spatially unbiased; within one district this is a property of $\pi^*$ given by Theorem 3 and is not restated, and across districts it is the present conclusion. $q\ge2$ is added because at $q=1$ the leading term vanishes and the hypotheses could not hold.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), p. ec6, proof of Theorem 6, last paragraph

import Mathlib
import Definitions.Def_CarlssonPartition_Equitable_Setting

open Filter Topology MeasureTheory

namespace CarlssonPartition.Equitable

theorem district_ratio (I : Instance) (hI : I.Standing) (hq : 2 ≤ I.q)
    (Rs : Fin I.m → Set Plane) (hP : I.IsPartition Rs)
    (h1 : ∀ i, (∫ x in Rs i, Real.sqrt (I.f x)) = (1 / (I.m : ℝ)) * ∫ x in I.R, Real.sqrt (I.f x))
    (h2 : ∀ i, (∫ x in Rs i, (I.sbar * I.v * (I.q : ℝ) + 2 * ‖x - I.x0‖) * I.f x)
      = (1 / (I.m : ℝ)) * ∫ x in I.R, (I.sbar * I.v * (I.q : ℝ) + 2 * ‖x - I.x0‖) * I.f x)
    (Tstar : ℝ → ℝ)
    (hstar : Tendsto (fun lam => Tstar lam / I.bvrLeading I.m lam I.R I.f)
      (I.heavy I.m I.R I.f) (𝓝 1))
    (T : Fin I.m → ℝ → ℝ)
    (hT : ∀ i, Tendsto (fun lam => T i lam / I.bvrLeading 1 (I.lamSub lam (Rs i)) (Rs i) (I.fSub (Rs i)))
      (I.heavy 1 (Rs i) (I.fSub (Rs i))) (𝓝 1)) :
    ∀ i, Tendsto (fun lam => T i lam / Tstar lam) (I.heavy I.m I.R I.f) (𝓝 1) := by sorry

end CarlssonPartition.Equitable

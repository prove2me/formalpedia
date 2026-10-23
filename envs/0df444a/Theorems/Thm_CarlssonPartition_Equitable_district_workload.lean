-- Prove2me | Theorems.Thm_CarlssonPartition_Equitable_district_workload
-- name    : CarlssonPartition.Equitable.district_workload
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-16T06:17:15.817113+00:00
-- url     : https://prove2.me/theorems/6e4ef62a-e8b7-4b1d-a12f-76a9a40566bb
-- title:
--   Proof of Theorem 6, p. ec6 — under the second equitable condition each district's workload factor equals the fleet's, so the heavy-traffic limits coincide
-- statement:
--   Let the instance satisfy the standing assumptions and let $\{\mathscr R_1,\dots,\mathscr R_m\}$ be a partition of $\mathscr R$. Fix a district $i$ with $\iint_{\mathscr R_i}f(x)\,dx>0$ that satisfies the second equitable condition
--   $$\iint_{\mathscr R_i}(\bar svq+2\|x-x_0\|)f(x)\,dx=\frac1m\iint_{\mathscr R}(\bar svq+2\|x-x_0\|)f(x)\,dx.$$
--   Write $\lambda_i=\lambda\iint_{\mathscr R_i}f$, $f_i=f/\iint_{\mathscr R_i}f$ and $\rho_i=\bar s\lambda_i$. Then for every arrival rate $\lambda$,
--   $$\rho_i+\frac{2\lambda_i\iint_{\mathscr R_i}\|x-x_0\|f_i(x)\,dx}{vq}=\frac{\lambda\left[\iint_{\mathscr R}(\bar svq+2\|x-x_0\|)f(x)\,dx\right]}{mvq}=\rho+\frac{2\lambda\iint_{\mathscr R}\|x-x_0\|f(x)\,dx}{mvq},$$
--   where $\rho=\lambda\bar s/m$. Consequently the district's heavy-traffic limit (its own workload factor tending to $1$ from below) is the same limit as the fleet's.
--
--   This is the step that lets Theorem 3, applied separately to each district with one vehicle, be read along the fleet's heavy-traffic limit: each district falls within the heavy-traffic regime exactly when the whole system does.
--
--   **Formalization Note.** The left-hand side is the workload factor $W_1(\lambda_i;\mathscr R_i,f_i)$ of the mission's `Setting`. The hypothesis $\iint_{\mathscr R_i}f>0$ is what the definition of $f_i$ presupposes. The coincidence of limits is stated as equality of the two `comap` filters.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), p. ec6, proof of Theorem 6, display after the chain

import Mathlib
import Definitions.Def_CarlssonPartition_Equitable_Setting

open Filter Topology MeasureTheory

namespace CarlssonPartition.Equitable

theorem district_workload (I : Instance) (hI : I.Standing)
    (Rs : Fin I.m → Set Plane) (hP : I.IsPartition Rs) (i : Fin I.m)
    (h2 : (∫ x in Rs i, (I.sbar * I.v * (I.q : ℝ) + 2 * ‖x - I.x0‖) * I.f x)
      = (1 / (I.m : ℝ)) * ∫ x in I.R, (I.sbar * I.v * (I.q : ℝ) + 2 * ‖x - I.x0‖) * I.f x)
    (hpos : 0 < I.pr (Rs i)) :
    (∀ lam : ℝ, I.workload 1 (I.lamSub lam (Rs i)) (Rs i) (I.fSub (Rs i))
      = lam * (∫ x in I.R, (I.sbar * I.v * (I.q : ℝ) + 2 * ‖x - I.x0‖) * I.f x)
          / ((I.m : ℝ) * I.v * (I.q : ℝ))) ∧
    (∀ lam : ℝ, I.workload 1 (I.lamSub lam (Rs i)) (Rs i) (I.fSub (Rs i))
      = I.workload I.m lam I.R I.f) ∧
    I.heavy 1 (Rs i) (I.fSub (Rs i)) = I.heavy I.m I.R I.f := by sorry

end CarlssonPartition.Equitable

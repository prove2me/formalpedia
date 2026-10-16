-- Prove2me | Theorems.Thm_CarlssonPartition_Equitable_district_leading
-- name    : CarlssonPartition.Equitable.district_leading
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:17:08.703915+00:00
-- url     : https://prove2.me/theorems/39a3c751-8723-411d-8092-58062a84a8cb
-- title:
--   Proof of Theorem 6, pp. ec5–ec6 — under both equitable conditions each district's Theorem 3 leading term equals the fleet's
-- statement:
--   Let the instance satisfy the standing assumptions and let $\{\mathscr R_1,\dots,\mathscr R_m\}$ be a partition of $\mathscr R$. Fix a district $i$ with $\iint_{\mathscr R_i}f(x)\,dx>0$ that satisfies both equitable conditions
--   $$\iint_{\mathscr R_i}\sqrt{f(x)}\,dx=\frac1m\iint_{\mathscr R}\sqrt{f(x)}\,dx,\qquad \iint_{\mathscr R_i}(\bar svq+2\|x-x_0\|)f(x)\,dx=\frac1m\iint_{\mathscr R}(\bar svq+2\|x-x_0\|)f(x)\,dx.$$
--   With $\lambda_i=\lambda\iint_{\mathscr R_i}f$, $f_i=f/\iint_{\mathscr R_i}f$ and $\rho_i=\bar s\lambda_i$, for every arrival rate $\lambda$,
--   $$\frac{\beta^2\lambda_i(1-\frac1q)^2\left[\iint_{\mathscr R_i}\sqrt{f_i(x)}\,dx\right]^2}{2v^2\left(1-\rho_i-\frac{2\lambda_i\iint_{\mathscr R_i}\|x-x_0\|f_i(x)\,dx}{vq}\right)^2}=\frac{\beta^2\lambda(1-\frac1q)^2\left[\iint_{\mathscr R}\sqrt{f(x)}\,dx\right]^2}{2m^2v^2\left(1-\rho-\frac{2\lambda\iint_{\mathscr R}\|x-x_0\|f(x)\,dx}{mvq}\right)^2}.$$
--
--   The left side is the leading-order delivery time that Theorem 3 (Bertsimas and van Ryzin) gives for one vehicle serving district $i$; the right side is the leading-order delivery time of the flexible fleet policy $\pi^*$. The identity is the chain of equalities in the proof of Theorem 6.
--
--   **Formalization Note.** Both sides are the `bvrLeading` term of the mission's `Setting`, with $(k,\lambda,S,g)=(1,\lambda_i,\mathscr R_i,f_i)$ on the left and $(m,\lambda,\mathscr R,f)$ on the right. It is an exact identity for every $\lambda$; the paper's "$\sim$" concerns the delivery time $T_i$, which does not appear here. The hypothesis $\iint_{\mathscr R_i}f>0$ is what the definition of $f_i$ presupposes.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), pp. ec5–ec6, proof of Theorem 6, chain of equalities

import Mathlib
import Definitions.Def_CarlssonPartition_Equitable_Setting

open Filter Topology MeasureTheory

namespace CarlssonPartition.Equitable

theorem district_leading (I : Instance) (hI : I.Standing)
    (Rs : Fin I.m → Set Plane) (hP : I.IsPartition Rs) (i : Fin I.m)
    (h1 : (∫ x in Rs i, Real.sqrt (I.f x)) = (1 / (I.m : ℝ)) * ∫ x in I.R, Real.sqrt (I.f x))
    (h2 : (∫ x in Rs i, (I.sbar * I.v * (I.q : ℝ) + 2 * ‖x - I.x0‖) * I.f x)
      = (1 / (I.m : ℝ)) * ∫ x in I.R, (I.sbar * I.v * (I.q : ℝ) + 2 * ‖x - I.x0‖) * I.f x)
    (hpos : 0 < I.pr (Rs i)) (lam : ℝ) :
    I.bvrLeading 1 (I.lamSub lam (Rs i)) (Rs i) (I.fSub (Rs i)) = I.bvrLeading I.m lam I.R I.f := by sorry

end CarlssonPartition.Equitable

-- Prove2me | Theorems.Thm_CarlssonPartition_Equitable_theorem_6
-- name    : CarlssonPartition.Equitable.theorem_6
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-16T06:17:14.763433+00:00
-- url     : https://prove2.me/theorems/36ba780a-dfa1-4e8d-89f2-2b5eb9e275c4
-- title:
--   Theorem 6, p. 11 — a partition equitable in ∬√f and ∬(s̄vq + 2‖x − x₀‖)f gives T/T(π*) → 1 in heavy traffic
-- statement:
--   Orders arrive at rate $\lambda$ at random points of a compact convex service region $\mathscr R\subseteq\mathbb R^2$ with demand density $f$, and are delivered from a depot $x_0\in\mathscr R$ by $m$ vehicles of speed $v$ and capacity $q\ge 2$, with mean on-site service time $\bar s$. Let $\{\mathscr R_1,\dots,\mathscr R_m\}$ be a partition of $\mathscr R$ that satisfies, for $i\in\{1,\dots,m\}$,
--   $$\iint_{\mathscr R_i}\sqrt{f(x)}\,dx=\frac1m\iint_{\mathscr R}\sqrt{f(x)}\,dx,\qquad \iint_{\mathscr R_i}(\bar svq+2\|x-x_0\|)f(x)\,dx=\frac1m\iint_{\mathscr R}(\bar svq+2\|x-x_0\|)f(x)\,dx.$$
--
--   Let $T(\pi^*)(\lambda)$ be the expected delivery time of the flexible policy $\pi^*$ of Bertsimas and van Ryzin, and $T_i(\lambda)$ that of an order in $\mathscr R_i$ when the vehicle dedicated to $\mathscr R_i$ runs the optimal single-vehicle policy there. Assume Theorem 3 for both:
--   1. $T(\pi^*)(\lambda)\sim\dfrac{\beta^2\lambda(1-\frac1q)^2\left[\iint_{\mathscr R}\sqrt{f}\right]^2}{2m^2v^2\left(1-\rho-2\lambda\iint_{\mathscr R}\|x-x_0\|f/mvq\right)^2}$ as $\rho+2\lambda\iint_{\mathscr R}\|x-x_0\|f/mvq\to1^-$, where $\rho=\lambda\bar s/m$;
--   2. for each $i$, $T_i(\lambda)\sim\dfrac{\beta^2\lambda_i(1-\frac1q)^2\left[\iint_{\mathscr R_i}\sqrt{f_i}\right]^2}{2v^2\left(1-\rho_i-2\lambda_i\iint_{\mathscr R_i}\|x-x_0\|f_i/vq\right)^2}$ as $\rho_i+2\lambda_i\iint_{\mathscr R_i}\|x-x_0\|f_i/vq\to1^-$, where $\lambda_i=\lambda\iint_{\mathscr R_i}f$, $f_i=f/\iint_{\mathscr R_i}f$ and $\rho_i=\bar s\lambda_i$.
--
--   Then the region partitioning policy, whose expected delivery time is $T=\sum_{i=1}^m\mathbb P(x\in\mathscr R_i)T_i$, is asymptotically optimal in heavy traffic:
--   $$\frac{\sum_{i=1}^m\mathbb P(x\in\mathscr R_i)\,T_i(\lambda)}{T(\pi^*)(\lambda)}\longrightarrow1\qquad\text{as }\rho+\frac{2\lambda\iint_{\mathscr R}\|x-x_0\|f(x)\,dx}{mvq}\to1^-.$$
--
--   Dedicating one driver to each district is operationally simpler than flexible dispatching; the theorem says it loses nothing to first order in heavy traffic provided the districts carry equal shares of the two measures $\iint\sqrt f$ and $\iint(\bar svq+2\|x-x_0\|)f$.
--
--   **Formalization Note.** The stochastic routing model is not formalized. "Every vehicle follows the optimal single-vehicle policy within the subregion" is encoded by hypothesis 2, Theorem 3 with $m=1$ in each district along the district's own heavy-traffic limit, exactly as the proofs on pp. ec4–ec6 use it; $T(\pi^*)$ and the $T_i$ are otherwise arbitrary real functions of $\lambda$. Every "$\sim$" is a ratio tending to $1$, and "asymptotically optimal" is the paper's definition $T(\pi)/T(\pi^*)\to1$ (p. 10). Heavy traffic is the filter of arrival rates $\lambda$ along which the workload factor tends to $1$ from below; all other data stay fixed. A partition is read up to null sets. The standing assumptions of §3 (compact convex $\mathscr R\ni x_0$, Lipschitz probability density, $m\ge1$, $v>0$, $\bar s\ge0$, $\beta>0$) are hypotheses. $q\ge2$ is an added hypothesis: at $q=1$ Theorem 3's leading term vanishes, so its ratio hypotheses could not hold and the theorem would be vacuous. Positivity of $\iint_{\mathscr R_i}f$ is not assumed; it follows from the first equitable condition.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), p. 11, Theorem 6 (with Theorem 3, p. 8, and the definition of asymptotic optimality, p. 10)

import Mathlib
import Definitions.Def_CarlssonPartition_Equitable_Setting

open Filter Topology MeasureTheory

namespace CarlssonPartition.Equitable

theorem theorem_6 (I : Instance) (hI : I.Standing) (hq : 2 ≤ I.q)
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
    Tendsto (fun lam => (∑ i, I.pr (Rs i) * T i lam) / Tstar lam) (I.heavy I.m I.R I.f) (𝓝 1) := by sorry

end CarlssonPartition.Equitable

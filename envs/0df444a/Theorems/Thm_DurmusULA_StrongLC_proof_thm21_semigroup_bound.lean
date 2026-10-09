-- Prove2me | Theorems.Thm_DurmusULA_StrongLC_proof_thm21_semigroup_bound
-- name    : DurmusULA.StrongLC.proof_thm21_semigroup_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:27.41085+00:00
-- url     : https://prove2.me/theorems/4a6bd747-802d-4c31-9239-1c696f5602f4
-- title:
--   §5.1, p. 34 — under L1 and H3(M_s), ‖P_t(x,·) − π‖_TV ≤ 2{3 + ‖x − x⋆‖ + ∫‖y − x⋆‖dπ(y)}κ^t
-- statement:
--   Let $U:\mathbb R^d\to\mathbb R$ satisfy **L1** (differentiable with $L$-Lipschitz gradient) and **H3($M_s$)** (convex, and $\langle\nabla U(x)-\nabla U(y),x-y\rangle\ge m\|x-y\|^2$ whenever $\|x-y\|\ge M_s$, with $M_s\ge0$, $m>0$). Let $x^\star$ be a minimiser of $U$, let $\pi\propto e^{-U}$, and let $(P_t)_{t\ge0}$ be the semigroup of the Langevin diffusion
--   $$dY_t=-\nabla U(Y_t)\,dt+\sqrt2\,dB^d_t .$$
--   Then for all $t\ge0$ and $x\in\mathbb R^d$,
--   $$\|P_t(x,\cdot)-\pi\|_{\mathrm{TV}}\le 2\Big\{3+\|x-x^\star\|+\int_{\mathbb R^d}\|y-x^\star\|\,d\pi(y)\Big\}\kappa^t ,$$
--   with $\kappa=\kappa_{21}$ the rate of Theorem 21,
--   $\log\kappa=-(m/2)\log2\,[\log\{(1+e^{m\omega(1/2,\max(1,M_s))/4})(1+\max(1,M_s))\}+\log2]^{-1}$.
--
--   This is the geometric ergodicity (3) of the Langevin semigroup with an explicit constant and rate; Theorem 21 inserts it into Proposition 2.
--
--   **Formalization Note** $x^\star$ is a bound variable with the hypothesis that it minimises $U$ (the paper uses $x^\star$ in §3.3 without defining it; in §§3.1–3.2 it is the minimiser). The integral $\int\|y-x^\star\|d\pi$ is a Bochner integral; it is finite under the hypotheses, and a junk value $0$ would only make the bound harder.
-- source:
--   Durmus and Moulines, Non-asymptotic convergence analysis for the Unadjusted Langevin Algorithm, arXiv:1507.05021v3, p. 34, §5.1, proof of Theorem 21, first display; L1 p. 3; H3 p. 15; (1) p. 1

import Mathlib
import Definitions.Def_DurmusULA_StrongLC_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal RealInnerProductSpace

namespace DurmusULA.StrongLC

theorem proof_thm21_semigroup_bound (d : ℕ) (U : EthierKurtz.SDEState d → ℝ) (L m Ms : ℝ)
    (xstar : EthierKurtz.SDEState d)
    (P : ℝ≥0 → EthierKurtz.SDEState d → Measure (EthierKurtz.SDEState d))
    (hL1 : L1 U L) (hH3 : H3 U m Ms) (hxstar : ∀ y, U xstar ≤ U y)
    (hP : IsDiffusionSemigroup (fun x => -gradient U x) (Real.sqrt 2) P) :
    ∀ (t : ℝ≥0) (x : EthierKurtz.SDEState d),
      tvNorm (P t x) (gibbs U) ≤
        2 * (3 + ‖x - xstar‖ + ∫ y, ‖y - xstar‖ ∂(gibbs U)) * kappa21 m Ms ^ (t : ℝ) := by sorry

end DurmusULA.StrongLC

-- Prove2me | Theorems.Thm_DurmusULA_StrongLC_theorem_21
-- name    : DurmusULA.StrongLC.theorem_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:18:29.470864+00:00
-- url     : https://prove2.me/theorems/8fce667e-3dd6-49bc-8b7b-450d245f1e0c
-- title:
--   Theorem 21, p. 16 — under L1 and H3(M_s), (10) holds with explicit κ, C(δ_xQ^n_γ) and A(γ, x)
-- statement:
--   Let $d\ge1$. Let $U:\mathbb R^d\to\mathbb R$ satisfy **L1** (differentiable, $\nabla U$ $L$-Lipschitz) and **H3($M_s$)** (convex, and $\langle\nabla U(x)-\nabla U(y),x-y\rangle\ge m\|x-y\|^2$ whenever $\|x-y\|\ge M_s$, with $M_s\ge0$, $m>0$). Let $x^\star$ minimise $U$, $\pi\propto e^{-U}$, and $(P_t)$ the Langevin semigroup of $dY_t=-\nabla U(Y_t)dt+\sqrt2dB^d_t$. Let $\bar\gamma\in(0,2mL^{-2})$ and let $(\gamma_k)_{k\ge1}$ be positive and nonincreasing with $\gamma_1\le\bar\gamma$. Put
--   $$\lambda=e^{-2m+\bar\gamma L^2},\quad c=2(d+mM_s^2),$$
--   $$\log\kappa=-\frac m2\log2\Big[\log\big\{(1+e^{m\omega(2^{-1},\max(1,M_s))/4})(1+\max(1,M_s))\big\}+\log2\Big]^{-1},$$
--   $$C_n=6+2(d/m+M_s^2)^{1/2}+2F^{1/2}(\lambda,\Gamma_{1,n},c,\gamma_1,\|x-x^\star\|^2),\qquad a=L^2G(\lambda,c,\gamma_1,\|x-x^\star\|^2),$$
--   with $F,G,\omega$ from (7), (8), (29). Then for all $n\ge0$, $p\ge1$, $n<p$ and $x\in\mathbb R^d$:
--   1. (3) holds at $\mu_0=\delta_xQ^n_\gamma$ with constant $C_n$: $\|\delta_xQ^n_\gamma P_t-\pi\|_{\mathrm{TV}}\le C_n\kappa^t$ for all $t>0$, i.e. $C(\delta_xQ^n_\gamma)\le C_n$;
--   2. $A(\gamma,x)\le a$, i.e. $\int\|\nabla U(z)\|^2Q^k_\gamma(x,dz)\le a$ for every $k\ge0$;
--   3. the bound (10) holds with these constants:
--   $$\|\delta_xQ^p_\gamma-\pi\|_{\mathrm{TV}}\le2^{-1/2}L\Big(\sum_{k=n}^{p-1}\Big\{\frac{\gamma_{k+1}^3}{3}a+d\gamma_{k+1}^2\Big\}\Big)^{1/2}+C_n\kappa^{\Gamma_{n+1,p}} .$$
--
--   The rate $\kappa$ does not depend on the dimension, and the bound is explicit in $d$; this is the paper's convergence guarantee for ULA when $U$ is strongly convex outside a ball.
--
--   **Formalization Note** The positive dimension binder matches the Euclidean setting and ensures Proposition 20's $c>0$. Total variation is the $\sup_{|f|\le1}$ norm (values in $[0,2]$). Moments are lower Lebesgue integrals. $x^\star$ is a bound variable with the hypothesis that it minimises $U$ (undefined in §3.3; the minimiser in §§3.1–3.2). Positivity of the steps is the standing assumption of p. 4. $\bar\gamma<2mL^{-2}$ is written $\bar\gamma L^2<2m$.
-- source:
--   Durmus and Moulines, Non-asymptotic convergence analysis for the Unadjusted Langevin Algorithm, arXiv:1507.05021v3, p. 16, Theorem 21 (with (10), p. 5, and Proposition 20, p. 16); proof §5.1, p. 34

import Mathlib
import Definitions.Def_DurmusULA_StrongLC_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal RealInnerProductSpace

namespace DurmusULA.StrongLC

theorem theorem_21 (d : ℕ) (U : EthierKurtz.SDEState d → ℝ) (L m Ms γbar : ℝ) (γ : ℕ → ℝ)
    (xstar : EthierKurtz.SDEState d)
    (P : ℝ≥0 → EthierKurtz.SDEState d → Measure (EthierKurtz.SDEState d))
    (hd : 0 < d) (hL1 : L1 U L) (hH3 : H3 U m Ms) (hxstar : ∀ y, U xstar ≤ U y)
    (hγbar : 0 < γbar) (hγbarL : γbar * L ^ 2 < 2 * m)
    (hγpos : ∀ k, 1 ≤ k → 0 < γ k) (hγmono : ∀ k, 1 ≤ k → γ (k + 1) ≤ γ k)
    (hγ1 : γ 1 ≤ γbar)
    (hP : IsDiffusionSemigroup (fun x => -gradient U x) (Real.sqrt 2) P) :
    ∀ (n p : ℕ) (x : EthierKurtz.SDEState d), 1 ≤ p → n < p →
      let lam := Real.exp (-2 * m + γbar * L ^ 2)
      let c := 2 * ((d : ℝ) + m * Ms ^ 2)
      let κ := kappa21 m Ms
      let V0 := ‖x - xstar‖ ^ 2
      let Cn := 6 + 2 * Real.sqrt ((d : ℝ) / m + Ms ^ 2) +
        2 * Real.sqrt (F lam (Gam γ 1 n) c (γ 1) V0)
      let a := L ^ 2 * G lam c (γ 1) V0
      (∀ t : ℝ≥0, 0 < t →
          tvNorm ((ulaLaw U γ x n).bind (P t)) (gibbs U) ≤ Cn * κ ^ (t : ℝ)) ∧
      (∀ k : ℕ, ∫⁻ z, ENNReal.ofReal (‖gradient U z‖ ^ 2) ∂(ulaLaw U γ x k) ≤
          ENNReal.ofReal a) ∧
      tvNorm (ulaLaw U γ x p) (gibbs U) ≤
        (Real.sqrt 2)⁻¹ * L *
            Real.sqrt (∑ k ∈ Finset.Ico n p, (γ (k + 1) ^ 3 / 3 * a + (d : ℝ) * γ (k + 1) ^ 2)) +
          Cn * κ ^ (Gam γ (n + 1) p) := by sorry

end DurmusULA.StrongLC

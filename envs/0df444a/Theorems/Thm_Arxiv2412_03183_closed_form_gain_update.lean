-- Prove2me | Theorems.Thm_Arxiv2412_03183_closed_form_gain_update
-- name    : Arxiv2412_03183.closed_form_gain_update
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T14:05:58.148881+00:00
-- url     : https://prove2.me/theorems/556f9636-0b41-4190-9115-b5ebfaafae60
-- title:
--   Eqs. (A4)-(A5): closed-form solution of the gain subproblem (A3) (under the conjugate-duplicated visibility convention)
-- statement:
--   Fix a non-negative image $x$, $\mu_1,\mu_2\ge0$, $\rho>0$ and gains $\hat h$. Assume that every visibility is recorded in both station orders with conjugate data: each $k\leftrightarrow(t_l,\alpha,\beta)$ has a partner $k'\leftrightarrow(t_l,\beta,\alpha)$ with $\tilde v_{k'}=\tilde v_k^*$, $\sigma_{k'}=\sigma_k$ and $(u_{k'},v_{k'})=(-u_k,-v_k)$. Let $a_{\alpha l},b_{\alpha l},c_{\alpha l},\eta_\alpha,r_{\alpha l}$ be as in eq. (A5), with $h=\hat h$, $y_k=\mathcal{F}_k(x)$ and $\mathcal{N}(\alpha l)$ the visibilities whose first gain is $g_{\alpha l}$. Assume $b_{\alpha l}\ne0$ and $r_{\alpha l}\ge0$ for all $(\alpha,l)$. Then
--
--   $$\hat g_{\alpha l}=r_{\alpha l}\frac{b_{\alpha l}}{|b_{\alpha l}|}$$
--
--   satisfies the constraint $\sum_l|\hat g_{\alpha l}|=N_\alpha$. It minimises the objective of eq. (A3),
--
--   $$\mathcal{L}_{\tilde v}(x,g,\hat h)+\mathcal{S}_{\mu_1,\mu_2}(g,\hat h)+\frac\rho2\sum_{\alpha,l}|g_{\alpha l}-\hat h_{\alpha l}|^2,$$
--
--   over all $g$ satisfying the constraint, and it is the only minimiser.
--
--   **Formalization Note** The paper states (A4)-(A5) without hypotheses. Three assumptions are added. (1) The conjugate-duplication convention. It is the only reading under which the printed data terms, with weight $1/\sigma_k^2$ and the single form $y_k\tilde v_k^*h_{\beta l}$, are correct. With each baseline recorded once, the printed formula is not the minimiser: a numerical counterexample is given in REPORT.md. (2) $b_{\alpha l}\ne0$, without which $b_{\alpha l}/|b_{\alpha l}|$ is undefined. (3) $r_{\alpha l}\ge0$. When some $r_{\alpha l}<0$ the paper sets $g_{\alpha l}=0$, which in general neither satisfies the constraint nor minimises (A3), so that case is not included. The paper calls (A3) "quadratic". This is not stated, because the $\mu_2$ terms and the constraint involve $|g_{\alpha l}|$.
-- source:
--   Ikeda, Nakazato, Tsukagoshi, Takeuchi and Yamaguchi, Solving Self-calibration of ALMA Data with an Optimization Method, arXiv:2412.03183v1 (2024), claim c025; Appendix 1, eqs. (A3)-(A5), PDF p. 9

import Mathlib
import Definitions.Def_Arxiv2412_03183_Basic

open Finset

namespace Arxiv2412_03183

theorem closed_form_gain_update {S : Type*} [Fintype S] [DecidableEq S] {N : S → ℕ}
    {M Nx Ny : ℕ} (D : ObsSetup S N M Nx Ny) (hdup : IsConjDuplicated D)
    (x : Image Nx Ny) (hx : x ∈ nonnegImages) (mu1 mu2 rho : ℝ) (hmu1 : 0 ≤ mu1)
    (hmu2 : 0 ≤ mu2) (hrho : 0 < rho) (h : Gains N)
    (hb : ∀ p, coefB D x mu1 rho h p ≠ 0) (hr : ∀ p, 0 ≤ coefR D x mu1 mu2 rho h p) :
    closedFormGain D x mu1 mu2 rho h ∈ gainFeasible N ∧
    IsMinOn (subproblemObjective D x mu1 mu2 rho h) (gainFeasible N)
      (closedFormGain D x mu1 mu2 rho h) ∧
    ∀ g ∈ gainFeasible N,
      subproblemObjective D x mu1 mu2 rho h g ≤
        subproblemObjective D x mu1 mu2 rho h (closedFormGain D x mu1 mu2 rho h) →
      g = closedFormGain D x mu1 mu2 rho h := by sorry

end Arxiv2412_03183

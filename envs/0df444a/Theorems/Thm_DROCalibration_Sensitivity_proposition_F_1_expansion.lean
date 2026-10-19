-- Prove2me | Theorems.Thm_DROCalibration_Sensitivity_proposition_F_1_expansion
-- name    : DROCalibration.Sensitivity.proposition_F_1_expansion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:18.310657+00:00
-- url     : https://prove2.me/theorems/079d95fa-6341-44c9-a223-2feea6295577
-- title:
--   Proposition F.1, (F.3), p. 47 — q_i(δ) = p_i{1 − δ(f_i − 𝔼_{ℙn}[f])/φ″(1)} + o(δ)
-- statement:
--   Fix a decision $x$, nominal probabilities $p_i>0$ with $\sum_i p_i=1$ (the empirical distribution is $p_i=1/n$) and rewards $f_i=f(x,Y_i)$. Let $\phi$ satisfy Assumption 2.1. Let $\delta\mapsto\mathbb Q(\delta)=(q_1(\delta),\dots,q_n(\delta))$ be any choice of minimizers of (2.7), i.e. for all sufficiently small $\delta>0$, $\mathbb Q(\delta)$ minimizes $\sum_iq_if_i+\frac1\delta\sum_ip_i\phi(q_i/p_i)$ over the probability simplex. Then for every $i$,
--   $$\lim_{\delta\downarrow0}\frac{q_i(\delta)-p_i}{\delta}=-\frac{p_i\big(f_i-\mathbb E_{\mathbb P_n}[f]\big)}{\phi''(1)},$$
--   that is,
--   $$q_i(\delta)=p_i\Big\{1-\frac{\delta}{\phi''(1)}\big(f_i-\mathbb E_{\mathbb P_n}[f]\big)\Big\}+o(\delta)\qquad(\delta\downarrow0).\quad\text{(F.3)}$$
--
--   The worst case moves mass away from the points with above-average reward, at a rate proportional to the deviation $f_i-\mathbb E_{\mathbb P_n}[f]$ and inversely proportional to the curvature $\phi''(1)$ of the divergence. Theorem 2.2 is obtained by summing these expansions against $f$.
--
--   **Formalization Note** The proposition's clause "$\mathbb Q(\delta)$ is continuously differentiable in a neighborhood of $\delta=0$" is not stated: only the one-sided derivative at $\delta=0$ in (F.3) is used by Theorem 2.2. The result holds for every selection of minimizers, which is at least as strong as the paper's statement about "the" minimizer (unique for small $\delta$ by Proposition F.1).
-- source:
--   Gotoh, Kim & Lim, Calibration of Distributionally Robust Empirical Optimization Models, arXiv:1711.06565v2, p. 47, Proposition F.1, (F.3)

import Mathlib
import Definitions.Def_DROCalibration_Sensitivity_Setting

open Filter Topology

namespace DROCalibration.Sensitivity

theorem proposition_F_1_expansion (φ : ℝ → EReal) (hφ : Assumption21 φ) {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1) (f : Fin n → ℝ) (Q : ℝ → Fin n → ℝ)
    (hQ : ∀ᶠ δ in 𝓝[>] 0, Q δ ∈ worstCaseSet φ p f δ) (i : Fin n) :
    Tendsto (fun δ => (Q δ i - p i) / δ) (𝓝[>] 0)
      (𝓝 (-(p i * (f i - wMean p f)) / phiPP φ)) := by sorry

end DROCalibration.Sensitivity

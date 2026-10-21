-- Prove2me | Theorems.Thm_DROCalibration_Sensitivity_theorem_2_2
-- name    : DROCalibration.Sensitivity.theorem_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:20.231657+00:00
-- url     : https://prove2.me/theorems/b36436c0-fcdf-44eb-911c-03d2893e5a9d
-- title:
--   Theorem 2.2, p. 8 — the worst-case sensitivity of the expected reward equals the variance under ℙ_n divided by φ''(1)
-- statement:
--   Fix a decision $x$, nominal probabilities $p_i>0$ with $\sum_ip_i=1$ (the paper's empirical distribution $\mathbb P_n$ is $p_i=1/n$) and rewards $f_i=f(x,Y_i)$, $i=1,\dots,n$. Let $\phi$ satisfy Assumption 2.1, and for $\delta>0$ let $\mathbb Q(\delta)$ be a worst-case measure of (2.7), that is, a minimizer over probability vectors $q$ of
--   $$\sum_{i=1}^n q_if_i+\frac1\delta\sum_{i=1}^n p_i\,\phi\!\left(\frac{q_i}{p_i}\right).$$
--   Then:
--
--   1. a worst-case measure $\mathbb Q(\delta)$ exists for every $\delta>0$;
--   2. for every choice of worst-case measures $\delta\mapsto\mathbb Q(\delta)$ (required for all sufficiently small $\delta>0$), the worst-case sensitivity (2.8) equals the variance divided by $\phi''(1)$:
--   $$\mathcal S_{\mathbb P_n}(f)=-\lim_{\delta\downarrow0}\frac{\mathbb E_{\mathbb Q(\delta)}[f]-\mathbb E_{\mathbb P_n}[f]}{\delta}=\frac{1}{\phi''(1)}\,\mathbb V_{\mathbb P_n}[f],$$
--   where $\mathbb E_{\mathbb P_n}[f]=\sum_ip_if_i$ and $\mathbb V_{\mathbb P_n}[f]=\sum_ip_i(f_i-\mathbb E_{\mathbb P_n}[f])^2$.
--
--   The theorem says that the penalized distributionally robust objective trades the expected reward against its variance: to first order in $\delta$, the worst case lowers the mean by $\delta\,\mathbb V_{\mathbb P_n}[f]/\phi''(1)$. This is the mechanism on which the paper's calibration of the robustness parameter $\delta$ rests.
--
--   **Formalization Note** The sensitivity is stated as the one-sided limit $\delta\downarrow0$ of the second line of (2.8), so the $\delta=0$ branch of (2.7) does not appear. The existence clause makes the statement non-vacuous, and the limit is asserted for every selection of minimizers rather than for "the" minimizer. Weights are general positive probabilities; $p_i=1/n$ gives the paper's $\frac1n\sum_i(f_i-\mathbb E_{\mathbb P_n}[f])^2$.
-- source:
--   Gotoh, Kim & Lim, Calibration of Distributionally Robust Empirical Optimization Models, arXiv:1711.06565v2, p. 8, Theorem 2.2

import Mathlib
import Definitions.Def_DROCalibration_Sensitivity_Setting

open Filter Topology

namespace DROCalibration.Sensitivity

theorem theorem_2_2 (φ : ℝ → EReal) (hφ : Assumption21 φ) {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1) (f : Fin n → ℝ) :
    (∀ δ : ℝ, 0 < δ → (worstCaseSet φ p f δ).Nonempty) ∧
    ∀ Q : ℝ → Fin n → ℝ, (∀ᶠ δ in 𝓝[>] 0, Q δ ∈ worstCaseSet φ p f δ) →
      Tendsto (fun δ => -((∑ i, Q δ i * f i) - wMean p f) / δ) (𝓝[>] 0)
        (𝓝 (wVar p f / phiPP φ)) := by sorry

end DROCalibration.Sensitivity

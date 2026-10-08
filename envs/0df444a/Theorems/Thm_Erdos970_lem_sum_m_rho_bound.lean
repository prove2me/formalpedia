-- Prove2me | Theorems.Thm_Erdos970_lem_sum_m_rho_bound
-- name    : Erdos970.lem_sum_m_rho_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:15:46.071858+00:00
-- url     : https://prove2.me/theorems/a1e75f63-eab7-4c14-b1ff-aec4f386e845
-- title:
--   Jensen-type bound — the zeros of f in |z| ≤ R₁, counted with multiplicity, number at most log B / log(R/R₁)
-- statement:
--   Let $B>1$ and $0<R_1<R<1$. Let $f:\mathbb C\to\mathbb C$ be analytic at every point of the closed unit disc, with $f(0)=1$ (in particular $f(0)\ne0$), and suppose the set $K$ of zeros of $f$ in the closed disc $|z|\le R_1$ (`zerosetKfR R₁ f`) is finite. Suppose $|f(z)|\le B$ for every $|z|\le R$, and that $h_\sigma$ is, for each zero $\sigma\in K$, a function analytic at $\sigma$ with $h_\sigma(\sigma)\ne0$ and $f(z)=(z-\sigma)^{m_\sigma}h_\sigma(z)$ near $\sigma$, where $m_\sigma$ is the order of vanishing of $f$ at $\sigma$. Then
--
--   $$\sum_{\rho\in K} m_\rho\;\le\;\frac{\log B}{\log(R/R_1)}.$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `Erdos970.lem_sum_m_rho_bound`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace Erdos970

open _root_.Filter
open Metric
open _root_.Set
open Bornology
open _root_.Function
open Classical

theorem lem_sum_m_rho_bound (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    (∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) ≤ (1/Real.log (R/R1)) * Real.log B := by
  sorry

end Erdos970

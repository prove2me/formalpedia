-- Prove2me | Theorems.Thm_Erdos970_lem_analytic_zero_factor
-- name    : Erdos970.lem_analytic_zero_factor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:04.517977+00:00
-- url     : https://prove2.me/theorems/1046727e-9280-4c95-85d0-abc83a6b3008
-- title:
--   Local factorization of an analytic function at a zero, with nonvanishing cofactor
-- statement:
--   Let $0<R_1<R<1$ and let $f:\mathbb C\to\mathbb C$ be analytic at every point of the closed unit disc $\{|z|\le1\}$ with $f(0)\ne0$. Let $\sigma$ be a zero of $f$ in the closed disc $\{|z|\le R_1\}$ (an element of the set `zerosetKfR R₁ f` of zeros of $f$ with $|z|\le R_1$). Then there is a function $h:\mathbb C\to\mathbb C$, analytic at $\sigma$ with $h(\sigma)\ne0$, such that for all $z$ in a neighbourhood of $\sigma$
--
--   $$f(z)=(z-\sigma)^{m}\,h(z),$$
--
--   where $m$ is the order of vanishing of $f$ at $\sigma$ (Mathlib's `analyticOrderAt f σ`, converted to a natural number; it is finite because $f$ is not identically zero near $0$). The hypothesis $R<1$ is not used beyond fixing the radii.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `Erdos970.lem_analytic_zero_factor`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace Erdos970

open _root_.Filter
open Metric
open _root_.Set
open Bornology
open _root_.Function
open Classical

theorem lem_analytic_zero_factor (R R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ) (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∃ h_σ : ℂ → ℂ, AnalyticAt ℂ h_σ σ ∧ h_σ σ ≠ 0 ∧
    ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ z := by
  sorry

end Erdos970

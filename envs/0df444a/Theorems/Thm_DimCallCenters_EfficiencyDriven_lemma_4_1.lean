-- Prove2me | Theorems.Thm_DimCallCenters_EfficiencyDriven_lemma_4_1
-- name    : DimCallCenters.EfficiencyDriven.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:42:27.651892+00:00
-- url     : https://prove2.me/theorems/eca2c8d7-4ad8-4e45-a684-183c0ce39be2
-- title:
--   Lemma 4.1 — Halfin–Whitt approximation
-- statement:
--   For positive offsets $x_\lambda$, the report gives three asymptotic statements for the continuous Erlang-C delay probability $\pi_\lambda$ and the delay function $P$. If $x_\lambda$ has finite limsup, then $\pi_\lambda(x_\lambda)/P(x_\lambda)\to1$. If also $x_\lambda\to x\ge0$, then $\pi_\lambda(x_\lambda)/P(x)\to1$. In particular,
--
--   $$
--   x_\lambda\to0\quad\Longrightarrow\quad\pi_\lambda(x_\lambda)\to1.
--   $$
--
--   All three clauses are part of the milestone; the final one is used directly in the efficiency-driven regime.
--
--   **Formalization Note** This concerns the report's continuous Erlang-C extension, including noninteger staffing levels. The formula extends $P$ to zero with value one.
-- source:
--   Borst, Mandelbaum & Reiman, Dimensioning Large Call Centers, CWI Report PNA-R0015 (2000), p. 15, Lemma 4.1

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_piLam
import Definitions.Def_DimCallCenters_Rationalized_delayFn

open Filter

namespace DimCallCenters.EfficiencyDriven

/-- Lemma 4.1 (Halfin and Whitt), p. 15: all three asymptotic claims. -/
theorem lemma_4_1 (μ : ℝ) (x : ℝ → ℝ) (hμ : 0 < μ)
    (hx : ∀ lam, 0 < lam → 0 < x lam) :
    ((∃ B : ℝ, ∀ᶠ lam in atTop, x lam ≤ B) →
      Tendsto (fun lam => DimCallCenters.Rationalized.piLam μ lam (x lam) / DimCallCenters.Rationalized.delayFn (x lam))
        atTop (nhds 1)) ∧
    (∀ x₀ : ℝ, 0 ≤ x₀ → Tendsto x atTop (nhds x₀) →
      Tendsto (fun lam => DimCallCenters.Rationalized.piLam μ lam (x lam) / DimCallCenters.Rationalized.delayFn x₀)
        atTop (nhds 1)) ∧
    (Tendsto x atTop (nhds 0) →
      Tendsto (fun lam => DimCallCenters.Rationalized.piLam μ lam (x lam)) atTop (nhds 1)) := by sorry

end DimCallCenters.EfficiencyDriven

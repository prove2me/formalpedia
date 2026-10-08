-- Prove2me | Theorems.Thm_AvgLMS_Expect_consequences_of_assumptions
-- name    : AvgLMS.Expect.consequences_of_assumptions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:05:28.084491+00:00
-- url     : https://prove2.me/theorems/67e839fb-8e3b-4a27-a24e-67a7fa0b0725
-- title:
--   App. A, p. 11 — (A6) gives E‖xₙ‖² ≤ R², tr H ≤ R², H ≼ (tr H)I ≼ R²I, and γH ≼ I for γ ≤ 1/R²
-- statement:
--   Assume (A1)–(A6). Then:
--   1. $\mathbb E\|x_n\|^2\le R^2$;
--   2. $\operatorname{tr}H\le R^2$;
--   3. $H\preccurlyeq(\operatorname{tr}H)\,I$ and $H\preccurlyeq R^2I$;
--   4. for every $\gamma\le1/R^2$, $\gamma H\preccurlyeq I$.
--
--   These are the "consequences of assumptions" recorded at the start of Appendix A. Item 4 is what makes the step-size condition $\gamma R^2\le1$ of the later lemmas meaningful: it guarantees that $I-\gamma H$ is a contraction on the spectrum of $H$.
--
--   **Formalization Note.** The inequalities against the identity are written as quadratic forms: $\langle v,Hv\rangle\le(\operatorname{tr}H)\|v\|^2$, $\langle v,Hv\rangle\le R^2\|v\|^2$ and $\gamma\langle v,Hv\rangle\le\|v\|^2$ for all $v$. The trace is the trace of $H$ as a linear map of $\mathbb R^d$.
-- source:
--   Bach & Moulines, arXiv:1306.2119v1, App. A, "Consequences of assumptions", p. 11

import Mathlib
import Definitions.Def_AvgLMS_Expect_Model

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace AvgLMS.Expect

/-- App. A, "Consequences of assumptions", p. 11: (A6) implies `E‖xₙ‖² ≤ R²`, `tr H ≤ R²`,
`H ≼ (tr H) I ≼ R² I`, and `γH ≼ I` whenever `γ ≤ 1/R²`. The Loewner inequalities against `I`
are written as quadratic-form inequalities. -/
theorem consequences_of_assumptions {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (x z : ℕ → Ω → Hs d) (H : Hs d →L[ℝ] Hs d) (θstar : Hs d) (R σ : ℝ)
    (hA : LMSAssumptions μ x z H θstar R σ) :
    ∫ ω, ‖x 1 ω‖ ^ 2 ∂μ ≤ R ^ 2 ∧
    LinearMap.trace ℝ (Hs d) (H : Hs d →ₗ[ℝ] Hs d) ≤ R ^ 2 ∧
    (∀ v : Hs d, ⟪v, H v⟫_ℝ ≤ LinearMap.trace ℝ (Hs d) (H : Hs d →ₗ[ℝ] Hs d) * ‖v‖ ^ 2) ∧
    (∀ v : Hs d, ⟪v, H v⟫_ℝ ≤ R ^ 2 * ‖v‖ ^ 2) ∧
    ∀ γ : ℝ, γ ≤ 1 / R ^ 2 → ∀ v : Hs d, γ * ⟪v, H v⟫_ℝ ≤ ‖v‖ ^ 2 := by sorry
end AvgLMS.Expect

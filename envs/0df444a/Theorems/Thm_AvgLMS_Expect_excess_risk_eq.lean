-- Prove2me | Theorems.Thm_AvgLMS_Expect_excess_risk_eq
-- name    : AvgLMS.Expect.excess_risk_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T11:05:24.537393+00:00
-- url     : https://prove2.me/theorems/9e8e6c43-bc72-4880-ab5b-820b623efc1c
-- title:
--   App. A, p. 11 — f(θ) − f(θ∗) = ½⟨θ − θ∗, H(θ − θ∗)⟩
-- statement:
--   Assume (A1)–(A6) (with $f$, $H$, $\theta^*$ as in the model). Then the excess risk of any point is a quadratic form in its deviation from $\theta^*$: for every $\theta\in\mathcal H$,
--   $$f(\theta)-f(\theta^*)=\tfrac12\,\langle\theta-\theta^*,\,H(\theta-\theta^*)\rangle.$$
--
--   In the paper this identity is used for $\theta=\theta_n$ and $\theta=\bar\theta_n$: it converts the expected excess risk of the averaged iterate into the quadratic form $\mathbb E\langle\bar\eta_{n-1},H\bar\eta_{n-1}\rangle$ of the deviation $\bar\eta_{n-1}=\bar\theta_{n-1}-\theta^*$, which is what the remaining lemmas bound.
--
--   **Formalization Note.** The statement is given for every deterministic $\theta$; the page's two instances follow by evaluating at $\theta_n(\omega)$ and $\bar\theta_n(\omega)$. The page prints $\tfrac12\langle\bar\eta_n,H\eta_n\rangle$ in the second instance; the intended $\tfrac12\langle\bar\eta_n,H\bar\eta_n\rangle$ is what the general form gives.
-- source:
--   Bach & Moulines, arXiv:1306.2119v1, App. A, first paragraph (after Eq. (12)), p. 11

import Mathlib
import Definitions.Def_AvgLMS_Expect_Model

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace AvgLMS.Expect

/-- App. A, p. 11: `f(θ) − f(θ∗) = ½⟨θ − θ∗, H(θ − θ∗)⟩` for every `θ` (the page states it for
`θₙ` and `θ̄ₙ`). -/
theorem excess_risk_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}
    (x z : ℕ → Ω → Hs d) (H : Hs d →L[ℝ] Hs d) (θstar : Hs d) (R σ : ℝ)
    (hA : LMSAssumptions μ x z H θstar R σ) :
    ∀ θ : Hs d, lsObjective μ x z θ - lsObjective μ x z θstar =
      (1 / 2) * ⟪θ - θstar, H (θ - θstar)⟫_ℝ := by sorry
end AvgLMS.Expect

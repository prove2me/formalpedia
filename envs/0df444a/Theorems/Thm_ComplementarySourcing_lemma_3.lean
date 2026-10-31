-- Prove2me | Theorems.Thm_ComplementarySourcing_lemma_3
-- name    : ComplementarySourcing.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:06:26.870338+00:00
-- url     : https://prove2.me/theorems/c72c1780-ad42-4fce-9ca6-d580657da083
-- title:
--   Lemma 3, p.13 — $x_1$, $x_2$ exist uniquely, $x_i\le\epsilon_i$, $x_1\ge x_2$
-- statement:
--   Let $\alpha\ge0$ and $0\le\sigma\le\epsilon_0$, and write $\epsilon_1=\epsilon_0+\sigma$, $\epsilon_2=\epsilon_0-\sigma$. There is exactly one $x_1\in[0,\epsilon_1]$ with
--
--   $$\frac{1+\alpha(2\epsilon_1-x_1)}{(1+\alpha x_1)^3}\,\epsilon_0=x_1,$$
--
--   and exactly one $x_2\in[0,\epsilon_2]$ with
--
--   $$\frac{1+\alpha(2\epsilon_2-x_2)}{(1+\alpha x_2)^3}\,\epsilon_2=x_2.$$
--
--   Furthermore $x_i\le\epsilon_i$ for $i=1,2$, and $x_1\ge x_2$.
--
--   These are the two candidates for the first mover's optimal effort, one for each region of efforts relative to the market risk.
--
--   Differences from the source:
--   - generalization: hypothesis rµ ≥ ϵ_1 + 2ϵ_0 → no such hypothesis, and no r, µ in the statement; reason: the conclusion does not involve r or µ and the proof on p.A2 does not use the hypothesis, so the printed case is a specialization
--   - reading: "Let x_1 be the unique value" → ∃! as a clause of the conclusion; reason: the page presupposes existence and uniqueness; they are stated so that later items may take x₁, x₂ as hypotheses
-- source:
--   Wang, Yin, Chen, Webster, Investment Efforts Under Complementary Sourcing, SSRN 3592730 (PDF of March 1, 2022), Lemma 3, p.13; proof p.A11 and Lemma A2, p.A2

import Mathlib
import Definitions.Def_ComplementarySourcing_IsEffortCandidate1
import Definitions.Def_ComplementarySourcing_IsEffortCandidate2

namespace ComplementarySourcing

/-- **Lemma 3** (Effort Bound): `x₁` is the unique value in `[0, ϵ₁]` with
`(1 + α(2ϵ₁ − x₁)) / (1 + αx₁)³ · ϵ₀ = x₁`, `x₂` is the unique value in `[0, ϵ₂]` with
`(1 + α(2ϵ₂ − x₂)) / (1 + αx₂)³ · ϵ₂ = x₂`, and `x_i ≤ ϵ_i`, `x₁ ≥ x₂`.
Wang, Yin, Chen, Webster, *Investment Efforts Under Complementary Sourcing*, SSRN 3592730
(PDF of March 1, 2022), Lemma 3, p.13 (PDF 13).

**Formalization Note.** The uniqueness the page presupposes is part of the statement. The printed
hypothesis `rµ ≥ ϵ₁ + 2ϵ₀` is not needed and is dropped. `ϵ₂ = 0` is allowed. -/
theorem lemma_3 {α ε₀ σ : ℝ} (hα : 0 ≤ α) (hσ₀ : 0 ≤ σ) (hσ : σ ≤ ε₀) :
    (∃! x, IsEffortCandidate1 α ε₀ σ x) ∧ (∃! x, IsEffortCandidate2 α ε₀ σ x) ∧
      ∀ x₁ x₂, IsEffortCandidate1 α ε₀ σ x₁ → IsEffortCandidate2 α ε₀ σ x₂ →
        x₁ ≤ ε₀ + σ ∧ x₂ ≤ ε₀ - σ ∧ x₁ ≥ x₂ := by sorry

end ComplementarySourcing

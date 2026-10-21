-- Prove2me | Theorems.Thm_AIFlywheel_Pricing_lemma_1
-- name    : AIFlywheel.Pricing.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:42.130391+00:00
-- url     : https://prove2.me/theorems/9b76e6cb-7b88-47cc-9c87-10fb4f8ffef2
-- title:
--   Lemma 1: the unique myopic data choice and expected revenue
-- statement:
--   Let $\nu>0$ be the data acquisition capacity and $\alpha>0$ an accuracy level. The second-period myopic revenue $R_\nu(\delta,\alpha)$, for $\delta\in[0,\nu]$, has the unique maximizing data quantity $\delta^M=\nu\bar F(\phi^{-1}(0))$, where $F$ is the standard uniform distribution, $\phi$ is its virtual value, and $\tau=\phi^{-1}(0)\bar F(\phi^{-1}(0))$. Its optimal value is
--   $$
--   J_{2b}(\alpha)=\alpha\tau.
--   $$
--   This identifies both the myopic quantity used after the last accuracy realization and the value used in the earlier-period objectives.
--
--   **Formalization Note.** The result is stated for every positive accuracy, including the paper's two accuracy levels. The dataset size $d_1$ does not enter the myopic problem.
-- source:
--   Gurkan & de Véricourt, Contracting, Pricing and Data Collection under the AI Flywheel Effect, ESMT Working Paper 20-01 (R3), August 17, 2021, p. 26 (PDF 27), Lemma 1; proof p. 27 (PDF 28).

import Mathlib
import Definitions.Def_AIFlywheel_Pricing_Model

namespace AIFlywheel.Pricing

/-- Lemma 1, p. 26: the myopic data choice and second-period value. -/
theorem lemma_1 (ν α : ℝ) (hν : 0 < ν) (hα : 0 < α) :
    deltaM ν ∈ Set.Icc 0 ν ∧
    (∀ δ ∈ Set.Icc 0 ν, revenue ν δ α ≤ revenue ν (deltaM ν) α) ∧
    (∀ δ ∈ Set.Icc 0 ν, revenue ν δ α = revenue ν (deltaM ν) α →
      δ = deltaM ν) ∧
    J2b ν α = α * tau := by sorry

end AIFlywheel.Pricing

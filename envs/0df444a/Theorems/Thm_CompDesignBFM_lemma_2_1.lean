-- Prove2me | Theorems.Thm_CompDesignBFM_lemma_2_1
-- name    : CompDesignBFM.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:26.04758+00:00
-- url     : https://prove2.me/theorems/ab85f24b-8595-4ff6-94cb-3c58497ff84e
-- title:
--   Lemma 2.1 (Myerson) — threshold payments make a monotone rule truthful and IR
-- statement:
--   Let $A$ be a deterministic monotone allocation rule. If every selected agent $i$ is paid the payment threshold $\tau_i(b_{-i})=\sup\{z\ge0:i\in A(z,b_{-i})\}$ and every other agent is paid zero, then the resulting mechanism is truthful and individually rational.
--
--   This is the classical characterization in single-parameter settings, used for the marginal-contribution branch.
--
--   Differences from the source:
--   - encoding: every selected agent is paid τ_i(b_-i) → hypothesis that each set {z ≥ 0 : i ∈ A(z, b_-i)} is bounded above; reason: a rule that always selects i has τ_i = +∞, where 'paid τ_i' is undefined; the condition excludes only that case
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Lemma 2.1, p.12 (PDF 14)

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneRule
import Definitions.Def_CompDesignBFM_thresholdMech
import Definitions.Def_CompDesignBFM_IsTruthful
import Definitions.Def_CompDesignBFM_IsIR

namespace CompDesignBFM

/-- Lemma 2.1 (Myerson), Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, p.12, PDF 14. A monotone allocation rule, with every selected agent paid
their threshold (5) and every other agent paid zero, is truthful and individually rational.
**Formalization Note.** The boundedness of the threshold sets excludes the case `τᵢ = +∞`, where "paid
`τᵢ`" has no meaning. -/
theorem lemma_2_1 {n : ℕ} (A : (Fin n → ℝ) → Finset (Fin n)) (hA : IsMonotoneRule A)
    (hbdd : ∀ b : Fin n → ℝ, (∀ j, 0 ≤ b j) → ∀ i,
      BddAbove {z : ℝ | 0 ≤ z ∧ i ∈ A (Function.update b i z)}) :
    IsTruthful (thresholdMech A) ∧ IsIR (thresholdMech A) := by sorry

end CompDesignBFM

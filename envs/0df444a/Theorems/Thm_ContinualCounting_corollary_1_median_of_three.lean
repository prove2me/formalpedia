-- Prove2me | Theorems.Thm_ContinualCounting_corollary_1_median_of_three
-- name    : ContinualCounting.corollary_1_median_of_three
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:42:16.440198+00:00
-- url     : https://prove2.me/theorems/4566e3df-195c-4e12-8245-552502b97880
-- title:
--   Corollary 1 [LPT21] — the median of three
-- statement:
--   Let $Z_1,Z_2,Z_3$ be i.i.d. real-valued random variables. Then
--   $$\mathbb E\big[\mathrm{median}\{Z_1,Z_2,Z_3\}^2\big]\le3\cdot\mathbb E[|Z_1|]^2.$$
--
--   The median of three copies turns control of the first absolute moment, which is what $\sigma$ provides, into control of a second moment, which is what orthogonal measurements need.
--
--   Differences from the source:
--   - encoding: real expectations → `lintegral` of `enorm` in ℝ≥0∞; reason: no integrability hypothesis is needed; if E|Z₁| = ∞ the right side is ∞
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), Corollary 1, p.10 (PDF p.11); proof App. B, pp.40–41 (PDF pp.41–42)

import Mathlib
import Definitions.Def_ContinualCounting_median3

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ContinualCounting

/-- **Corollary 1 [LPT21] (median of three).** Bairaktari, Dahl, Larsen, arXiv:2607.00876 (sha256
986e6426…), p.10: "Let Z1, Z2, Z3 be i.i.d. real-valued random variables. Then
E[median{Z1, Z2, Z3}^2] ≤ 3 · E[|Z1|]^2."

**Formalization Note.** On an arbitrary probability space, in `ℝ≥0∞`: no integrability hypothesis is
needed, and both sides may be `∞`. -/
theorem corollary_1_median_of_three {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : Fin 3 → Ω → ℝ) (hmeas : ∀ k, Measurable (Z k))
    (hindep : ProbabilityTheory.iIndepFun Z P)
    (hid : ∀ k, ProbabilityTheory.IdentDistrib (Z k) (Z 0) P P) :
    ∫⁻ ω, ‖median3 (Z 0 ω) (Z 1 ω) (Z 2 ω)‖ₑ ^ 2 ∂P ≤ 3 * (∫⁻ ω, ‖Z 0 ω‖ₑ ∂P) ^ 2 := by sorry

end ContinualCounting

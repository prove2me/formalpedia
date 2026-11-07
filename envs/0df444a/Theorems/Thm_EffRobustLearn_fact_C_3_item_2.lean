-- Prove2me | Theorems.Thm_EffRobustLearn_fact_C_3_item_2
-- name    : EffRobustLearn.fact_C_3_item_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:35:04.901924+00:00
-- url     : https://prove2.me/theorems/e6b4a961-19e6-49d7-a89b-82de4b400d42
-- title:
--   Fact C.3 item 2 — $R_{|S|,D}(H)\le C_1\sqrt{\mathrm{VCdim}(H)/|S|}$
-- statement:
--   There is a universal constant $C_1>0$ such that, for every distribution $D$, every class $H\subseteq\{\pm1\}^X$ of finite VC dimension and every sample size $|S|\ge1$,
--   $$R_{|S|,D}(H)\le C_1\sqrt{\frac{\mathrm{VCdim}(H)}{|S|}}.$$
--
--   **Formalization Note** The bound holds at every fixed sample, so it passes to the integral. For a non-integrable integrand the Bochner integral is $0$ and the bound is trivial.
--
--   Differences from the source:
--   - reading: every class $H$ → $\mathrm{vcDim}\,H<\top$; reason: for infinite VC dimension the right side is $\infty$
--   - encoding: $E[\sup]$ over the sample → Bochner integral of the published empirical complexity; reason: no change on integrable integrands
--   - encoding: $H\subseteq\{\pm1\}^X$ → $H$ Boolean, cast by toPM; reason: same class
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Fact C.3 item 2, p.41 (PDF p.42), cited from [Wai19, Example 5.24]

import Mathlib
import Definitions.Def_UnderstandingML_VC
import Definitions.Def_EffRobustLearn_toPM
import Definitions.Def_EffRobustLearn_rademacherD

open MeasureTheory

namespace EffRobustLearn

universe u

/-- Fact C.3 item 2, p.41 (arXiv:2609.17655, held version, sha256 312a0857…), cited from [Wai19, Example 5.24]: `R_{|S|,D}(H) ≤ C₁ √(VCdim(H)/|S|)`, `C₁` universal.

**Formalization Note.** "For every class" is read for `vcDim H < ⊤`: for infinite VC dimension the right side is `∞`. No measurability is assumed, as in the paper: the bound holds at every fixed sample, so it passes to the integral `R` whenever the integrand is integrable, and otherwise the Bochner integral is `0`. For a measurable pointwise separable class, the case the mission uses, the integrand is measurable and bounded. -/
theorem fact_C_3_item_2 :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ (X : Type u) [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
        (H : Set (X → Bool)), UnderstandingML.vcDim H < ⊤ → ∀ n : ℕ, 0 < n →
          rademacherD D n (toPM '' H) ≤
            C₁ * Real.sqrt (((UnderstandingML.vcDim H).toNat : ℝ) / (n : ℝ)) := by sorry

end EffRobustLearn

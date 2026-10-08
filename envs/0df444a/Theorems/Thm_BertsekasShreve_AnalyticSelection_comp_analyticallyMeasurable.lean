-- Prove2me | Theorems.Thm_BertsekasShreve_AnalyticSelection_comp_analyticallyMeasurable
-- name    : BertsekasShreve.AnalyticSelection.comp_analyticallyMeasurable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T00:50:54.156157+00:00
-- url     : https://prove2.me/theorems/053de957-a9ba-4027-b1fc-c8f878bb539b
-- title:
--   Corollary 7.44.2 — composites of analytically measurable functions are universally measurable
-- statement:
--   Let $X$, $Y$ and $Z$ be Borel spaces, $D\in\mathscr A_X$ and $E\in\mathscr A_Y$. Suppose $f:D\to Y$ and $g:E\to Z$ are analytically measurable and $f(D)\subseteq E$. Then:
--
--   1. the composition $g\circ f:D\to Z$ is universally measurable;
--   2. for every $A\in\mathscr A_Y$, the set $f^{-1}(A)$ belongs to $\mathscr U_X$.
--
--   The composite of two analytically measurable functions need not be analytically measurable, so this is the strongest measurability that survives composition; it is what makes the exact selector of Proposition 7.50(b) universally measurable.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 172, Corollary 7.44.2

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_BorelSpace
import Definitions.Def_BertsekasShreve_AnalyticSelection_Measurability

open MeasureTheory

namespace BertsekasShreve.AnalyticSelection

/-- **Corollary 7.44.2** (p. 172). Let `X`, `Y`, `Z` be Borel spaces, `D ∈ 𝒜_X`, `E ∈ 𝒜_Y`, and
`f : D → Y`, `g : E → Z` analytically measurable with `f(D) ⊆ E`. Then `g ∘ f` is universally
measurable, and `f⁻¹(A) ∈ 𝒰_X` for every `A ∈ 𝒜_Y`. -/
theorem comp_analyticallyMeasurable {X Y Z : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [IsBorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [IsBorelSpace Y]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] [IsBorelSpace Z]
    (D : Set X) (E : Set Y) (hD : IsAnalyticallyMeasurable D) (hE : IsAnalyticallyMeasurable E)
    (f : D → Y) (g : E → Z)
    (hf : IsAnalyticallyMeasurableFun D f) (hg : IsAnalyticallyMeasurableFun E g)
    (hfE : ∀ x : D, f x ∈ E) :
    IsUniversallyMeasurableFun D (fun x : D => g ⟨f x, hfE x⟩) ∧
    ∀ A : Set Y, IsAnalyticallyMeasurable A →
      IsUniversallyMeasurable (Subtype.val '' (f ⁻¹' A)) := by sorry

end BertsekasShreve.AnalyticSelection

-- Prove2me | Theorems.Thm_BertsekasShreve_AnalyticSelection_image_preimage_analytic
-- name    : BertsekasShreve.AnalyticSelection.image_preimage_analytic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T00:50:20.414337+00:00
-- url     : https://prove2.me/theorems/98bbd0f8-fdc0-4125-80c4-1e5cf3b8c3e6
-- title:
--   Proposition 7.40 — Borel-measurable images and preimages of analytic sets are analytic
-- statement:
--   Let $X$ and $Y$ be Borel spaces and $f:X\to Y$ a Borel-measurable function. Then
--
--   1. for every analytic set $A\subseteq X$, the image $f(A)$ is analytic;
--   2. for every analytic set $B\subseteq Y$, the preimage $f^{-1}(B)$ is analytic.
--
--   This shows that analyticity depends only on the Borel structure, and it is used to transport analytic sets along the Borel maps of a dynamic programming model.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 165, Proposition 7.40

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_BorelSpace

open MeasureTheory

namespace BertsekasShreve.AnalyticSelection

/-- **Proposition 7.40** (p. 165). Let `X`, `Y` be Borel spaces and `f : X → Y` Borel-measurable.
Images of analytic subsets of `X` and preimages of analytic subsets of `Y` are analytic. -/
theorem image_preimage_analytic {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [IsBorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [IsBorelSpace Y]
    (f : X → Y) (hf : Measurable f) :
    (∀ A : Set X, AnalyticSet A → AnalyticSet (f '' A)) ∧
    (∀ B : Set Y, AnalyticSet B → AnalyticSet (f ⁻¹' B)) := by sorry

end BertsekasShreve.AnalyticSelection

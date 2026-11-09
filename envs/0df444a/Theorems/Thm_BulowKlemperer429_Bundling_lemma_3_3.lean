-- Prove2me | Theorems.Thm_BulowKlemperer429_Bundling_lemma_3_3
-- name    : BulowKlemperer429.Bundling.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:45:20.912211+00:00
-- url     : https://prove2.me/theorems/77c75b7a-4df7-4f71-97cc-d5655ecbf72c
-- title:
--   Lemma 3.3 — tensorization of independent-copy variation
-- statement:
--   Let $V=(V_j)_{j\in\iota}$ have finitely many independent real-valued coordinates with laws $\nu_j$, and let $h:\mathbb R^\iota\to\mathbb R$ satisfy $\mathbb E|h(V)|<\infty$. Then
--   $$G(h(V))\le\sum_{j\in\iota}\mathbb E_{V_{-j}}\big[G(h(V_{-j},V_j))\big].$$
--   Inside each $G$, only coordinate $j$ is resampled independently and the other coordinates are held fixed. This combines the scalar comparisons without requiring nonnegative or bounded coordinates.
--
--   **Formalization Note** Integrability is exactly the source hypothesis. Nonintegrable slices can occur only on a null set; their Bochner-integral default does not change the outer expectation.
--
--   Differences from the source:
--   - encoding: coordinates indexed 1 through m and outer expectation over V_{-j} → an arbitrary finite index type and an outer integral over the full product law of a function independent of coordinate j; reason: integrating the unused coordinate contributes total mass one; this is the same expectation, including empty and singleton index sets
--   - encoding: coordinate replacement notation → Function.update, with a decidable equality instance on the finite index type; reason: finite sets admit decidable equality and no mathematical instance is excluded
-- source:
--   Yichen Huang, STOC 2027 submission #429 (October 2026), p. 9, Lemma 3.3 (PDF p. 10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/429.pdf

import Mathlib
import Definitions.Def_BulowKlemperer429_Bundling_Variation
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace BulowKlemperer429.Bundling

theorem lemma_3_3 {ι : Type} [Fintype ι] [DecidableEq ι]
    (ν : ι → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)]
    (h : (ι → ℝ) → ℝ) (hint : Integrable h (Measure.pi ν)) :
    variation (Measure.pi ν) h ≤
      ∑ j, ∫ v, variation (ν j) (fun x => h (Function.update v j x)) ∂Measure.pi ν := by sorry

end BulowKlemperer429.Bundling

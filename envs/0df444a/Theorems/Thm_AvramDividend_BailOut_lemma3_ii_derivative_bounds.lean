-- Prove2me | Theorems.Thm_AvramDividend_BailOut_lemma3_ii_derivative_bounds
-- name    : AvramDividend.BailOut.lemma3_ii_derivative_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:07:34.620725+00:00
-- url     : https://prove2.me/theorems/4833c887-a60c-4795-96c0-f35c8824a818
-- title:
--   Lemma 3(ii) — $1\le\bar v'_{d^*}\le\varphi$ and the boundary slopes
-- statement:
--   Let $X$ be a spectrally negative Lévy process satisfying the standing assumptions. Let $q>0$, $\varphi>1$, and let $\bar v_{d^*}$ be the candidate value (5.4) at the barrier level $d^*$ of (5.6). Then:
--
--   1. for every $x>0$, $\;1\le\bar v_{d^*}'(x)\le\varphi$;
--   2. if $d^*>0$, the left derivative of $\bar v_{d^*}$ at $d^*$ equals $1$;
--   3. if $d^*>0$, the right derivative of $\bar v_{d^*}$ at $0$ equals $\varphi$ when $X$ has unbounded variation, and exists and is strictly less than $\varphi$ when $X$ has bounded variation.
--
--   These slope bounds give the conditions $1-w'\le0$ and $w'\le\varphi$ of the variational inequality (5.9) for $w=\bar v_{d^*}$.
--
--   **Formalization Note** $\bar v_{d^*}'(x)$ is `deriv`, the one-sided derivatives are `HasDerivWithinAt` on $(-\infty,d^*]$ and on $[0,\infty)$. Unbounded variation is the negation of bounded variation. The lemma's header "Let $x,a>0$" concerns only $x$ here.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, p. 16, Lemma 3(ii)

import Mathlib
import Definitions.Def_AvramDividend_BailOut_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_BailOut_ScaleFunction
import Definitions.Def_AvramDividend_BailOut_BarrierCandidates

open MeasureTheory
open scoped NNReal ENNReal

namespace AvramDividend.BailOut

theorem lemma3_ii_derivative_bounds {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (Lv : SpectrallyNegativeLevy P 𝓕) (hL : Lv.StandingAssumptions)
    {q : ℝ} (hq : 0 < q) {φ : ℝ} (hφ : 1 < φ)
    {W : ℝ → ℝ} (hW : Lv.triplet.IsScaleFunction q W) :
    (∀ x : ℝ, 0 < x →
        1 ≤ deriv (vbar Lv q φ W (dStar q φ W).toReal) x ∧
          deriv (vbar Lv q φ W (dStar q φ W).toReal) x ≤ φ) ∧
      (0 < dStar q φ W →
        HasDerivWithinAt (vbar Lv q φ W (dStar q φ W).toReal) 1
            (Set.Iic (dStar q φ W).toReal) (dStar q φ W).toReal ∧
          (¬ Lv.triplet.BoundedVariation →
            HasDerivWithinAt (vbar Lv q φ W (dStar q φ W).toReal) φ (Set.Ici 0) 0) ∧
          (Lv.triplet.BoundedVariation →
            ∃ D : ℝ, HasDerivWithinAt (vbar Lv q φ W (dStar q φ W).toReal) D (Set.Ici 0) 0 ∧
              D < φ)) := by sorry

end AvramDividend.BailOut

-- Prove2me | Theorems.Thm_AvramDividend_BailOut_lemma2_ii_dstar_zero_iff
-- name    : AvramDividend.BailOut.lemma2_ii_dstar_zero_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:06:33.204309+00:00
-- url     : https://prove2.me/theorems/4a349bea-17df-4651-b2bc-e263b9d4a45b
-- title:
--   Lemma 2(ii) — $d^*=0$ iff $\sigma=0$ and $\nu(-\infty,0)\le q/(\varphi-1)$
-- statement:
--   Let $X$ be a spectrally negative Lévy process with Gaussian coefficient $\sigma$ and Lévy measure $\nu$ satisfying the standing assumptions. Let $q>0$, $\varphi>1$, let $W^{(q)}$ be its $q$-scale function, and let $d^*=\inf\{a>0:G(a)\le0\}$ be the barrier level of (5.6). Then:
--
--   1. if $\sigma=0$ and $\nu(-\infty,0)\le q/(\varphi-1)$, then $d^*=0$;
--   2. otherwise $d^*>0$.
--
--   It separates the case where the optimal policy keeps the risk process at zero from the case of a genuine upper barrier.
--
--   **Formalization Note** $\nu(-\infty,0)$ may be infinite and is compared in $[0,\infty]$. $d^*$ is an element of $[0,\infty]$.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, p. 15, Lemma 2(ii)

import Mathlib
import Definitions.Def_AvramDividend_BailOut_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_BailOut_ScaleFunction
import Definitions.Def_AvramDividend_BailOut_BarrierCandidates

open MeasureTheory
open scoped NNReal ENNReal

namespace AvramDividend.BailOut

theorem lemma2_ii_dstar_zero_iff {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (Lv : SpectrallyNegativeLevy P 𝓕) (hL : Lv.StandingAssumptions)
    {q : ℝ} (hq : 0 < q) {φ : ℝ} (hφ : 1 < φ)
    {W : ℝ → ℝ} (hW : Lv.triplet.IsScaleFunction q W) :
    (Lv.triplet.σ = 0 ∧ Lv.triplet.ν (Set.Iio 0) ≤ ENNReal.ofReal (q / (φ - 1)) →
        dStar q φ W = 0) ∧
      (¬ (Lv.triplet.σ = 0 ∧ Lv.triplet.ν (Set.Iio 0) ≤ ENNReal.ofReal (q / (φ - 1))) →
        0 < dStar q φ W) := by sorry

end AvramDividend.BailOut

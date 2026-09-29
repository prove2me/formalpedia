-- Prove2me | Theorems.Thm_AvramDividend_BailOut_lemma5_generator_inequality
-- name    : AvramDividend.BailOut.lemma5_generator_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:09:32.370348+00:00
-- url     : https://prove2.me/theorems/77eb8588-ac41-4a3d-9dcc-ab234d5f1cdd
-- title:
--   Lemma 5 — $(\Gamma\bar v_{d^*}-q\bar v_{d^*})(x)\le0$ for $x>0$, $=0$ on $(0,d^*)$
-- statement:
--   Let $X$ be a spectrally negative Lévy process with triplet $(c,\sigma,\nu)$ and generator $\Gamma$, satisfying the standing assumptions. Let $q>0$, $\varphi>1$. Let $\bar v_{d^*}$ be the candidate value (5.4) at the level $d^*$ of (5.6), extended to $x<0$ by $\bar v_{d^*}(x)=\bar v_{d^*}(0)+\varphi x$. Then:
--
--   1. for every $x>0$, the integrand of $\Gamma\bar v_{d^*}(x)$ is $\nu$-integrable and
--   $$(\Gamma\bar v_{d^*}-q\bar v_{d^*})(x)\le 0;$$
--   2. if $d^*>0$, then $(\Gamma\bar v_{d^*}-q\bar v_{d^*})(x)=0$ for every $x\in(0,d^*)$.
--
--   With Lemma 3(ii) this shows that $\bar v_{d^*}$ satisfies the variational inequality (5.9).
--
--   **Formalization Note** The paper prints the extension as $\bar v_{d^*}(x)=\bar v_{d^*}(x)+\varphi x$; the intended $\bar v_{d^*}(0)+\varphi x$ is what formula (5.4) gives for $x<0$, and it is used here. Integrability of the generator's integrand is stated as part of the conclusion, because the paper applies $\Gamma$ to $\bar v_{d^*}$ as an element of its domain.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, p. 20, Lemma 5 (extension of v̄_{d*} to x < 0 on p. 20)

import Mathlib
import Definitions.Def_AvramDividend_BailOut_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_BailOut_ScaleFunction
import Definitions.Def_AvramDividend_BailOut_BarrierCandidates

open MeasureTheory
open scoped NNReal ENNReal

namespace AvramDividend.BailOut

theorem lemma5_generator_inequality {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (Lv : SpectrallyNegativeLevy P 𝓕) (hL : Lv.StandingAssumptions)
    {q : ℝ} (hq : 0 < q) {φ : ℝ} (hφ : 1 < φ)
    {W : ℝ → ℝ} (hW : Lv.triplet.IsScaleFunction q W) :
    (∀ x : ℝ, 0 < x →
        Integrable (fun y => vbar Lv q φ W (dStar q φ W).toReal (x + y) -
            vbar Lv q φ W (dStar q φ W).toReal x -
            (if |y| < 1 then deriv (vbar Lv q φ W (dStar q φ W).toReal) x * y else 0))
          Lv.triplet.ν ∧
        generator Lv.triplet (vbar Lv q φ W (dStar q φ W).toReal) x -
            q * vbar Lv q φ W (dStar q φ W).toReal x ≤ 0) ∧
      (0 < dStar q φ W → ∀ x ∈ Set.Ioo 0 (dStar q φ W).toReal,
        generator Lv.triplet (vbar Lv q φ W (dStar q φ W).toReal) x -
            q * vbar Lv q φ W (dStar q φ W).toReal x = 0) := by sorry

end AvramDividend.BailOut

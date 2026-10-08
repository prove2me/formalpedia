-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrier_cstar_verification_upper_bounds
-- name    : AvramDividend.Classical.barrier_cstar_verification_upper_bounds
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T23:25:45.735984+00:00
-- url     : https://prove2.me/theorems/11dd5aff-472a-4930-bb6e-8922374e16f1
-- title:
--   Verification bounds at the finite optimal barrier, with unrestricted bound under generator inequality
-- statement:
--   Under the standing assumptions, positive discount rate, scale-function identity, finite optimal barrier, and the smoothness condition of Theorem 2, the candidate barrier value is an upper bound for the supremum of admissible dividend values with reserve cap c*. If the generator residual is nonpositive above c* and integrable there, the candidate also bounds the unrestricted dividend value function for every initial surplus x >= 0. This is the verification-inequality component of Theorem 2. The analytic proof uses generator equality below the barrier, derivative >= 1, regularity of the barrier candidate, the bounded-cap verification proposition and its whole-line version, including x > c*. The theorem states the difficult comparison inequalities independently of attaining the bounds with a barrier policy.
-- source:
--   Avram, Palmowski and Pistorius (2007), On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Lemmas 3-4, Proposition 4(i), Theorem 2(i)-(ii) (pp.14-21).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrier_cstar_verification_upper_bounds {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    (∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x)) ∧
    ((∀ y : ℝ, (cstar W).toReal < y →
       X.GeneratorIntegrable (vcstar W) y ∧
         X.generator (vcstar W) y - q * vcstar W y ≤ 0) →
      ∀ x : ℝ, 0 ≤ x →
        valueFunction X q x ≤ ENNReal.ofReal (vcstar W x)) := by sorry

end AvramDividend.Classical

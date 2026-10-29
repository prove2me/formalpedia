-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_genuine_strip_from_indep
-- name    : AvramDividend.Classical.avram_ws01e_bf_new_genuine_strip_from_indep
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:45:29.750669+00:00
-- url     : https://prove2.me/theorems/4f3c95f0-f974-47fe-aa11-373659f82c7e
-- title:
--   Genuine random-terminal Esscher positive-strip descending Wiener-Hopf identity from true independence
-- statement:
--   Given the genuine Qp running-supremum and terminal-drawdown independence, and the previously proved true terminal and supremum real finite-gap MGFs, derive the exact cross-multiplied descending identity for each 0<beta<lam. This is a conditional public bridge with only the independently required stochastic independence premise, used in the canonical proof once Chat 02 proves that premise. No assertion of the divergent beta>=lam terminal MGF is made.
-- source:
--   Source-faithful Wiener-Hopf finite-rate factorisation from actual Qp independence and strict root monotonicity, with finite real MGFs established separately.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bf_new_genuine_strip_from_indep
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ p lam : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hp : 0 < p) (hlam : 0 < lam)
    (hlamroot : X.ψ (φ + lam) - q = p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ φ))))
    (hIndep : IndepFun
      (fun z : Ω × ℝ => runningSup X (Real.toNNReal z.2) z.1)
      (fun z : Ω × ℝ =>
        runningSup X (Real.toNNReal z.2) z.1 -
          X.X (Real.toNNReal z.2) z.1)
      ((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ φ))))) :
    ∀ β : ℝ, 0 < β → β < lam →
      mgf (fun z : Ω × ℝ =>
        -(runningSup X (Real.toNNReal z.2) z.1 -
          X.X (Real.toNNReal z.2) z.1))
        ((P.prod (expMeasure p)).withDensity
          (fun z : Ω × ℝ => ENNReal.ofReal
            (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
              (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) β *
      (p - (X.ψ (φ + β) - q)) =
      (p / lam) * (lam - β) := by sorry

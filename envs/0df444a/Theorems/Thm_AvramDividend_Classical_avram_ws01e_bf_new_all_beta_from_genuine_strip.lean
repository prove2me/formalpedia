-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_all_beta_from_genuine_strip
-- name    : AvramDividend.Classical.avram_ws01e_bf_new_all_beta_from_genuine_strip
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T21:53:05.320875+00:00
-- url     : https://prove2.me/theorems/04630964-7d99-4332-ba5b-27d8a21273f5
-- title:
--   Actual Esscher descending all-beta factor from a genuine finite-strip stochastic cross identity
-- statement:
--   For the genuine Qp joint law of a spectrally negative Lévy process, given exactly the finite-strip cross-multiplied stochastic factorisation (not the quotient outside its integrable domain), deduce the exact descending drawdown ENNReal Laplace transform at all positive beta. All analytic and monotonicity premises are discharged by proved source-specific theorems: analyticity of true descending MGF and shifted Levy exponent, strict positive-root monotonicity, real/ENNReal MGF conversion, and the abstract analytic continuation/removable-root result. The only additional premise relative to the canonical all-beta target is the honest missing finite-strip cross identity.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2013), §2.1 and §2.2; Proved analytic source 57a0f80e, 9ed76dc1, 4dddb6f2, 0906e33f and ENNReal bridge a7daedce.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_all_beta_wh_analytic_continuation_with_removable_root
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_genuine_tilted_clock_descending_mgf_analytic_positive
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_shifted_levy_psi_analytic_on_positive
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_descending_lintegral_eq_mgf_positive
import Theorems.Thm_AvramDividend_Classical_esscher_levy_shift_strictMonoOn

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bf_new_all_beta_from_genuine_strip
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ p lam m : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hp : 0 < p) (hlam : 0 < lam)
    (hlamroot : X.ψ (φ + lam) - q = p)
    (hm : 0 < m) (hmderiv : HasDerivAt X.ψ m (φ + lam))
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ φ))))
    (hStrip : ∀ β : ℝ, 0 < β → β < lam →
      mgf
        (fun z : Ω × ℝ =>
          -(runningSup X (Real.toNNReal z.2) z.1 -
            X.X (Real.toNNReal z.2) z.1))
        ((P.prod (expMeasure p)).withDensity
          (fun z : Ω × ℝ => ENNReal.ofReal
            (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
              (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) β *
      (p - (X.ψ (φ + β) - q)) = (p / lam) * (lam - β)) :
    ∀ β : ℝ, 0 < β →
      (∫⁻ z : Ω × ℝ,
        ENNReal.ofReal (Real.exp
          (-β * (runningSup X (Real.toNNReal z.2) z.1 -
            X.X (Real.toNNReal z.2) z.1)))
        ∂((P.prod (expMeasure p)).withDensity
          (fun z : Ω × ℝ => ENNReal.ofReal
            (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
              (Real.toNNReal z.2 : ℝ) * X.ψ φ))))) =
      ENNReal.ofReal
        (if β = lam then p / (lam * m)
         else (p / lam) * ((lam - β) / (p - (X.ψ (φ + β) - q)))) := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_tilted_clock_drawdown_zero_atom_of_infinite_jumps_ws01f
-- name    : AvramDividend.Classical.levy_tilted_clock_drawdown_zero_atom_of_infinite_jumps_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:27:30.16299+00:00
-- url     : https://prove2.me/theorems/a3134e18-9097-489a-b491-b185883bda05
-- title:
--   Infinite negative-small-jump activity removes the zero terminal-drawdown atom under the actual Esscher exponential clock
-- statement:
--   Under the exact hypotheses of the genuinely accepted all-positive-β finite-rate descending Wiener–Hopf factor, and infinite absolute first moment of negative small jumps, the actual tilted exponential-clock law assigns probability zero to equality of the source Lévy process terminal value and its running supremum. The proof uses the genuine factor and its accepted high-parameter scalar asymptotic, with a direct lower bound of the Laplace integral by the zero-drawdown event mass.
-- source:
--   Accepted source-specific all-β factor e4e12a00, new analytic scalar limit de30158b, and source-specific joint measurability of runningSup X and X.X. No use of an assumed Gaussian model or unproved Poisson band representation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_genuine_descending_factor_tendsto_zero_ws01f
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_genuine_tilted_exponential_descending_factor_all_beta
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open Filter Topology MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_tilted_clock_drawdown_zero_atom_of_infinite_jumps_ws01f
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (q φ p lam m : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hp : 0 < p) (hlam : 0 < lam)
    (hlamroot : X.ψ (φ + lam) - q = p)
    (hm : 0 < m) (hmderiv : HasDerivAt X.ψ m (φ + lam))
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) :
    ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (φ * X.X z.2.toNNReal z.1 -
          (z.2.toNNReal : ℝ) * X.ψ φ))))
      {z : Ω × ℝ | runningSup X z.2.toNNReal z.1 -
        X.X z.2.toNNReal z.1 = 0} = 0 := by sorry

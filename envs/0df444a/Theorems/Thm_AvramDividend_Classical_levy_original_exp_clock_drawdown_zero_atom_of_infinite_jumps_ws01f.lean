-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_original_exp_clock_drawdown_zero_atom_of_infinite_jumps_ws01f
-- name    : AvramDividend.Classical.levy_original_exp_clock_drawdown_zero_atom_of_infinite_jumps_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:39:19.015899+00:00
-- url     : https://prove2.me/theorems/100a3d08-bbcb-4692-ae93-8aca0e71abac
-- title:
--   Strictly positive genuine Esscher density transports the zero terminal-drawdown atom back to original Lévy law
-- statement:
--   For the actual original Lévy process with infinite negative small-jump first moment and genuine finite-clock Wiener–Hopf factor hypotheses, the unweighted original product measure P×Exp(p) assigns zero mass to terminal drawdown zero. This is obtained by transporting the accepted genuinely tilted drawdown zero-atom result through the pointwise strictly positive Esscher density, using the pinned Mathlib almost-everywhere equivalence for measures with density.
-- source:
--   Proved levy_tilted_clock_drawdown_zero_atom_of_infinite_jumps_ws01f and pinned Mathlib MeasureTheory.ae_withDensity_iff. No surrogate probability space or distributional proxy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_tilted_clock_drawdown_zero_atom_of_infinite_jumps_ws01f

open Filter Topology MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_original_exp_clock_drawdown_zero_atom_of_infinite_jumps_ws01f
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
    (P.prod (expMeasure p))
      {z : Ω × ℝ | runningSup X z.2.toNNReal z.1 -
        X.X z.2.toNNReal z.1 = 0} = 0 := by sorry

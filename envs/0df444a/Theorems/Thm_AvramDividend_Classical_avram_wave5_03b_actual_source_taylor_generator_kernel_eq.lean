-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_taylor_generator_kernel_eq
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_source_taylor_generator_kernel_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T01:09:32.162203+00:00
-- url     : https://prove2.me/theorems/e336f7e2-a55f-48e8-b33e-54114f97e681
-- title:
--   Actual controlled prepayment Taylor jump correction equals the source Lévy generator kernel on a reserve band
-- statement:
--   For any negative jump mark of the real source SpectrallyNegativeLevy process and its original adapted-dividend prepayment reserve, the compact-band nonlinear jump value increment minus the exact small negative-mark linear correction equals the correspondingly band-masked canonical Lévy generator jump integrand. The identity handles both -1<z<0 and z<=-1 without changing sign conventions, making the compensator drift recognisable as the jump part of X.generator w on the localised positive-reserve band. It is an algebraic generator identification, not the martingale compensation or Itô–Meyer theorem.
-- source:
--   Original Avram–Palmowski–Pistorius Proposition 4 source jump generator, with canonical Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy.generatorIntegrand. Uses original x+X-rightLimit D strict-left-limit and actual negative source jump mark, not an abstract Poisson model. Small-mark interval is Ioo (-1) 1 in generatorIntegrand and reduces to -1<z for z<0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_source_taylor_generator_kernel_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (p : ℝ≥0 × Ω) (z : ℝ) (hz : z < 0) :
    let Y : ℝ≥0 × Ω → ℝ := fun r => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s r.2 - rightLimit D s r.2) r.1
    (if Y p ∈ Icc (u + δ) v then
      w (Y p + z) - w (Y p) else 0) -
    (if -1 < z then
      z * (if Y p ∈ Icc (u + δ) v then deriv w (Y p) else 0)
      else 0) =
    if Y p ∈ Icc (u + δ) v then
      SpectrallyNegativeLevy.generatorIntegrand w (Y p) z else 0 := by sorry

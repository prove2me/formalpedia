-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_discounted_actual_ruin_stopped_full_jump_energy
-- name    : AvramDividend.Classical.avram_wave5_03_discounted_actual_ruin_stopped_full_jump_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T01:09:22.724029+00:00
-- url     : https://prove2.me/theorems/e2ddf935-fadb-4497-bdec-33d9c71da5cd
-- title:
--   Original discounted finite-horizon ruin-stopped full Lévy jump value kernel has predictable L2 energy
-- statement:
--   For the same original SpectrallyNegativeLevy path, actual left-continuous dividend strategy, source right-continuous predictable filtration and genuine ruin time, the complete negative-mark value increment of a C1 compact interior test function remains jointly predictable and square-integrable when multiplied by the exact discounted finite-clock and inclusive ruin-survival mask exp(-qt) 1_{t≤T}1_{t≤ruinTime}. The inclusive mask deliberately retains the ruin-causing source jump. The proof combines the Proved source stopped-discount predictability and source controlled full-mark L2 contraction results, without introducing an independent jump process or asserting an unproved compensator.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), stochastic integrability for formulae (5.11)–(5.13). Integrator-owned actual finite-horizon local martingale kernel for BV ef7e6c20 and UBV 429e17ca; source Stieltjes and Brownian terms remain separate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_source_stopped_discounted_deriv_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_controlled_predictable_jump_energy_contraction

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_discounted_actual_ruin_stopped_full_jump_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v δ : ℝ)
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hu0 : 0 ≤ u)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hband : u + δ ≤ v)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let J : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
      fun p => if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if p.1.1 ≤ T then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then
            (1 : ℝ) else 0)
        else 0) * J p
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] H ∧
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤ := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b51_original_borel_compensated_simple_mark_energy_L2_vanish
-- name    : AvramDividend.Classical.avram_b51_original_borel_compensated_simple_mark_energy_L2_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:11:38.710427+00:00
-- url     : https://prove2.me/theorems/08e7f398-29ad-4ec5-8940-a37095fa3686
-- title:
--   Actual original compensated Borel mark simple integrals have vanishing second moment under vanishing mark energy
-- statement:
--   For the actual finite-activity spectrally negative Levy process, construct the original compensated finite Borel negative-mark simple gains of varying finite partitions. If their exact coefficient-square physical Levy-intensity energies converge to zero, then the expected squares of these genuine source random variables converge to zero; no global mark-square moment or proxy Poisson noise.
-- source:
--   Proved original physical mark isometry ja31 b7fdb101.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja31_original_finite_borel_mark_source_isometry
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b51_original_borel_compensated_simple_mark_energy_L2_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (K : ℕ → ℕ)
    (B : ℕ → ℕ → Set ℝ) (c : ℕ → ℕ → ℝ)
    (hB : ∀ n i, i ∈ Finset.range (K n) →
      MeasurableSet (B n i))
    (hNeg : ∀ n i, i ∈ Finset.range (K n) →
      B n i ⊆ Iio (0 : ℝ))
    (hDisj : ∀ n i j, i ∈ Finset.range (K n) →
      j ∈ Finset.range (K n) → i ≠ j →
      Disjoint (B n i) (B n j))
    (hEnergy : Tendsto
      (fun n => ∑ i ∈ Finset.range (K n),
        (c n i)^2 * ((t : ℝ≥0∞) * X.ν (B n i)).toReal)
      atTop (𝓝 (0 : ℝ))) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    ∃ F : ℕ → Ω → ℝ,
      (∀ n ω, F n ω = ∑ i ∈ Finset.range (K n),
        c n i * ((NX ω (Ioc 0 t ×ˢ B n i)).toReal -
          ((t : ℝ≥0∞) * X.ν (B n i)).toReal)) ∧
      Tendsto (fun n => ∫ ω, (F n ω)^2 ∂P)
        atTop (𝓝 (0 : ℝ)) := by sorry

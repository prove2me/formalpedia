-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja24_original_marked_strip_second_moment_of_L2
-- name    : AvramDividend.Classical.avram_ja24_original_marked_strip_second_moment_of_L2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T17:44:43.258804+00:00
-- url     : https://prove2.me/theorems/ec5fe7b6-c09f-4d4d-835f-97171aad2c25
-- title:
--   Original compensated marked strip has exact second moment once square-integrable
-- statement:
--   For the original source process and a finite negative jump activity assumption, any square-integrable compensated original marked jump strip has the exact Levy strip square variance. The extra quadratic integrability premise separates the physical mark isometry from the elementary integrability obtained by bounding the original finite-activity jump count. There is no auxiliary Brownian space or change of law.
-- source:
--   True physical source; prerequisites for 924b87ab and 9a1c9ee4; verified Proved 63088608 finite marked-count isometry and 0af54511 finite step isometry, requiring genuinely justified mark-simple approximation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja24_original_marked_strip_second_moment_of_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n m : ℕ), n ≤ m → ∀ (t : ℝ≥0),
      let S : Set ℝ :=
        Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      let C : Ω → ℝ := fun ω =>
        (∫ p in (Ioc 0 t ×ˢ S), p.2 ∂NX ω) -
          (t : ℝ) * (∫ z in S, z ∂X.ν)
      Integrable (fun ω => (C ω) ^ 2) P →
      (∫ ω, (C ω) ^ 2 ∂P) =
        (t : ℝ) * (∫ z in S, z ^ 2 ∂X.ν) := by sorry

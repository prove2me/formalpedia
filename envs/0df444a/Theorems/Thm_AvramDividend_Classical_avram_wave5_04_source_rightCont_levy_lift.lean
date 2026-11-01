-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
-- name    : AvramDividend.Classical.avram_wave5_04_source_rightCont_levy_lift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T01:12:03.508201+00:00
-- url     : https://prove2.me/theorems/e58a099d-9977-4265-9e76-7a5f0f6aa758
-- title:
--   Original Lévy source lifts unchanged to its right-continuous filtration
-- statement:
--   For the exact given spectrally negative Lévy process X on probability P and filtration F, there is a process Y on F.rightCont with literally identical sample paths, drift, Gaussian coefficient and jump measure. Stationary increments, Laplace transform and path properties are inherited without a copy or extension of probability space; the original X retains independent increments under F.rightCont by the previously proved right-continuous independence theorem. This bridges the original controlled predictable energy on F.rightCont and source-jump compensation statements parameterised by a Levy process' own filtration. It does not itself prove the missing source predictable rectangle compensator or Ito-Meyer formula.
-- source:
--   Mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43 BV positive-cap verification ef7e6c20. Canonical source definition 933ced80; Proved right-continuous independent increments baf51c16 and adapted monotonicity as used in Proved bd2bcc87. Same original X and P, exact path and triplet fields.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_indepIncrements_rightCont

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04_source_rightCont_levy_lift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ Y : SpectrallyNegativeLevy P 𝓕.rightCont,
      Y.X = X.X ∧ Y.c = X.c ∧ Y.σ = X.σ ∧ Y.ν = X.ν := by sorry

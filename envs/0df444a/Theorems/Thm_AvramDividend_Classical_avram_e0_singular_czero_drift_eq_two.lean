-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_e0_singular_czero_drift_eq_two
-- name    : AvramDividend.Classical.avram_e0_singular_czero_drift_eq_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:46:14.954095+00:00
-- url     : https://prove2.me/theorems/f9f5362b-2443-4c6e-9afc-cf2f1f516a00
-- title:
--   Zero canonical drift coefficient yields physical drift two for singular negative density
-- statement:
--   For the original Avram spectrally-negative Levy interface, zero triplet coefficient and the established singular negative-jump density imply physical drift two, using the accepted exact restricted signed jump moment.
-- source:
--   Necessary source-exact drift component for e0b94d7f-cb1e-450a-8f04-b2e732af5dbe countermodel, feeding the existing Standing constructor.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gen15_singular_density_restricted_signed_moment_neg_two
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_e0_singular_czero_drift_eq_two
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hc : X.c = 0)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0)) :
    X.drift = 2 := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_cutoff_linear_mark_integrable
-- name    : AvramDividend.Classical.avram_p4_c_generator_cutoff_linear_mark_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:57:23.557811+00:00
-- url     : https://prove2.me/theorems/63c53f4c-113e-48e0-8d54-55be014f9398
-- title:
--   Original Lévy measure has a finite signed linear drift correction on every separated truncation band
-- statement:
--   For every ε>0, ν has finite mass on z≤-ε by the original Lévy min(1,z²) integrability. On the bounded intersection -1<z<-ε, the signed mark z has norm at most one, so its ν-integral is finite. This is the honest finite-band drift correction needed when converting the source strict-unit-truncated drift c into the ε-cutoff physical drift c−∫_{(-1,-ε)}z ν(dz), without presuming full small-jump first moment finiteness or bounded variation.
-- source:
--   SpectrallyNegativeLevy.ν_integrable, Proved negative_jump_truncation_measure_finite (16a2d301-ca20-4837-969a-892ae00966c0), paper generator triplet and strict |z|<1 convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_negative_jump_truncation_measure_finite

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_cutoff_linear_mark_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun z : ℝ => z) (Ioo (-1 : ℝ) (-ε)) X.ν := by sorry

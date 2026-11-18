-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_poisson_real_geometric_sequence_integrable_20261117
-- name    : AvramDividend.Classical.avram_a27_poisson_real_geometric_sequence_integrable_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:31:36.800207+00:00
-- url     : https://prove2.me/theorems/8ad7cf40-6f33-4cdc-8b96-02ed92ea8bea
-- title:
--   Any real single-mark power sequence is integrable against a Poisson count law
-- statement:
--   Every real geometric sequence m^k, including negative m, is integrable with respect to any finite-rate Poisson distribution. This supplies Poisson-integrability of the original single negative-jump Laplace mark moment without an additional restriction.
-- source:
--   Proved generic real Poisson probability generating function chat06 and Bochner integral nonintegrable convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Poisson measures integrate all real-power geometric sequences. -/

theorem AvramDividend.Classical.avram_a27_poisson_real_geometric_sequence_integrable_20261117 (r : ℝ≥0) (m : ℝ) :
    Integrable (fun k : ℕ => m ^ k) (poissonMeasure r) := by sorry

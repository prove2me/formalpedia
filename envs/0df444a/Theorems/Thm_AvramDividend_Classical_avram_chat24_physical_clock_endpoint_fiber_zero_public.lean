-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_physical_clock_endpoint_fiber_zero_public
-- name    : AvramDividend.Classical.avram_chat24_physical_clock_endpoint_fiber_zero_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T14:05:29.540603+00:00
-- url     : https://prove2.me/theorems/a1bf7f56-8c85-4124-bb47-180fa4590e76
-- title:
--   Physical time-clock endpoint fiber has zero integral
-- statement:
--   Deterministic physical-time ingredient for 7c376a84-b0d3-4cc5-bbcb-57bdc43931aa. The pushforward of Lebesgue restricted to [0,T] under toNNReal has no atoms, including at zero. Any function supported at a single endpoint therefore has zero integral; no integrability assumption is needed. Published as a public prerequisite because the authoritative parent is public and public candidates cannot import private helper declarations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_chat24_physical_clock_endpoint_fiber_zero_public
    (T : ℝ) (t : ℝ≥0) (f : ℝ≥0 → ℝ) :
    let μ : Measure ℝ≥0 := (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    (∫ s, if s = t then f s else 0 ∂μ) = 0 := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_d_bvmesh_integrable_taylor_error_expectation_le
-- name    : AvramDividend.Classical.avram_p3_d_bvmesh_integrable_taylor_error_expectation_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:56:48.517531+00:00
-- url     : https://prove2.me/theorems/90182f3d-ab28-4cd0-90ed-6b1addd03d5f
-- title:
--   L1 expectation domination of a localised BV finite-grid Taylor remainder
-- statement:
--   For any original probability or finite base measure, once the actual localised finite-grid source Taylor remainder and its total-variation envelope are integrable and the absolute pathwise error is bounded almost surely by epsilon times the envelope, its L1 expectation is at most epsilon times the expected envelope. This is the minimal justified step from a.e. mesh error to expected mesh error. It asserts no unproved compensation, zero martingale mean or optional stopping.
-- source:
--   After the finite-grid pathwise jump-separated Taylor budget of P3-D and P3-C's Proved original frozen-source grid 837277c5, the remaining passage to expectation is an integral monotonicity argument under explicit L1 conditions. The original P3 prebudget's expectation is at the same P, with integrability to be discharged by stopped local variation. The inequality does not assert that this envelope is integrable for the original X by fiat.

import Mathlib
open MeasureTheory

theorem AvramDividend.Classical.avram_p3_d_bvmesh_integrable_taylor_error_expectation_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (err B : Ω → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (herr : Integrable err P) (hB : Integrable B P)
    (hbound : ∀ᵐ ω ∂P, |err ω| ≤ ε * B ω) :
    (∫ ω, |err ω| ∂P) ≤ ε * (∫ ω, B ω ∂P) := by sorry

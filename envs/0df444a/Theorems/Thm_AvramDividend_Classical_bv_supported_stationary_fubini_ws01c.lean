-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_supported_stationary_fubini_ws01c
-- name    : AvramDividend.Classical.bv_supported_stationary_fubini_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T11:48:23.155172+00:00
-- url     : https://prove2.me/theorems/c0cd917e-a627-4981-bc37-0016a78f952f
-- title:
--   Supported-time Fubini transfer of a stationary almost-sure path event
-- statement:
--   A jointly measurable event holds at almost every time on almost every path. If the nonzero sigma-finite time measure is supported on B and the probability-one status of the event is invariant among times in B and a distinguished time t₀, then the event holds at t₀ almost surely. Fubini exchanges the a.e. quantifiers; nonzero measure selects a supported time. This rigorously avoids requiring stationarity for negative time.
-- source:
--   Fubini/Tonelli a.e. quantifier commutation for sigma-finite measures; used for the positive-time derivative Cauchy event in bounded-variation Lévy no-creeping WS01C. Source work/avram_ws01c_supported_fubini_transfer_draft.lean.

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Restrict

open MeasureTheory Set Filter

theorem AvramDividend.Classical.bv_supported_stationary_fubini_ws01c
    {T Ω : Type*} [MeasurableSpace T] [MeasurableSpace Ω]
    (μ : Measure T) (P : Measure Ω)
    [SFinite μ] [SFinite P] [NeZero μ]
    (B : Set T) (hSupport : ∀ᵐ t ∂μ, t ∈ B)
    (t₀ : T) (A : T → Ω → Prop)
    (hMeas : MeasurableSet {z : T × Ω | A z.1 z.2})
    (hPath : ∀ᵐ ω ∂P, ∀ᵐ t ∂μ, A t ω)
    (hStationary : ∀ t ∈ B,
      (∀ᵐ ω ∂P, A t ω) ↔ (∀ᵐ ω ∂P, A t₀ ω)) :
    ∀ᵐ ω ∂P, A t₀ ω := by sorry

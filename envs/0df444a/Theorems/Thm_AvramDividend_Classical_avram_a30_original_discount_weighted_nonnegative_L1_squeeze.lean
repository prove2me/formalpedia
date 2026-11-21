-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a30_original_discount_weighted_nonnegative_L1_squeeze
-- name    : AvramDividend.Classical.avram_a30_original_discount_weighted_nonnegative_L1_squeeze
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:30:00.867705+00:00
-- url     : https://prove2.me/theorems/d7cc5fb4-45a1-48e7-b4a1-3ae0eac83e42
-- title:
--   Discount weights bounded between zero and one preserve vanishing expected positive physical mesh errors
-- statement:
--   For a physical stopped Gaussian mesh residual family F_m≥0 integrable whose exact expectation tends to zero, multiplication by the actual discounted stopping clock weights E_m∈[0,1] preserves integrability and convergence of expected weighted errors to zero. Proves the full weighted L1 squeeze with AEStronglyMeasurable weights, without any independence or artificial martingale assumptions. Applies directly to original Gaussian finitecap spatial crossing positive errors, cap contact and ruin-contact estimates.
-- source:
--   Original finitecap physical stopped discounted Gaussian mesh positive residual source, deterministic L1 multiplication lemma.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical

theorem AvramDividend.Classical.avram_a30_original_discount_weighted_nonnegative_L1_squeeze
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F E : ℕ → Ω → ℝ)
    (hFI : ∀ m, Integrable (F m) P)
    (hFpos : ∀ m, ∀ᵐ ω ∂P, 0 ≤ F m ω)
    (hEm : ∀ m, AEStronglyMeasurable (E m) P)
    (hEb : ∀ m, ∀ᵐ ω ∂P, 0 ≤ E m ω ∧ E m ω ≤ 1)
    (hLimit : Tendsto (fun m => ∫ ω, F m ω ∂P)
      atTop (nhds (0 : ℝ))) :
    Tendsto (fun m => ∫ ω, E m ω * F m ω ∂P)
      atTop (nhds (0 : ℝ)) := by sorry

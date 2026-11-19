-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_ae_signed_mesh_error_vanish_implies_cash_upper
-- name    : AvramDividend.Classical.avram_ja18_ae_signed_mesh_error_vanish_implies_cash_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:20:57.56921+00:00
-- url     : https://prove2.me/theorems/36fa4a78-62f6-4e38-bcfc-f8e9d7966236
-- title:
--   Signed mesh nonpositive drift and vanishing errors give a genuine pointwise cash upper bound
-- statement:
--   On one common conull set, each mesh has a nonpositive signed HJB/dividend remainder, an error tending to zero, and a cash inequality with two fixed genuine noise limits. Taking the limit yields a pathwise cash inequality with exactly those two noises. This is the analytic final-limit transfer required for a source-faithful mixed Gaussian/jump stopped Ito-Meyer ledger.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ja18_ae_signed_mesh_error_vanish_implies_cash_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (F G J : Ω → ℝ) (c : ℝ)
    (B E : ℕ → Ω → ℝ)
    (hB : ∀ᵐ ω ∂(P.restrict A), ∀ m : ℕ, B m ω ≤ 0)
    (hE : ∀ᵐ ω ∂(P.restrict A),
      Tendsto (fun m => E m ω) atTop (nhds (0 : ℝ)))
    (hCash : ∀ᵐ ω ∂(P.restrict A), ∀ m : ℕ,
      F ω ≤ c + G ω + J ω + B m ω + E m ω) :
    ∀ᵐ ω ∂(P.restrict A), F ω ≤ c + G ω + J ω := by sorry

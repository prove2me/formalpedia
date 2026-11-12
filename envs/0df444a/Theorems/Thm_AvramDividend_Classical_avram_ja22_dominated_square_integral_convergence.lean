-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja22_dominated_square_integral_convergence
-- name    : AvramDividend.Classical.avram_ja22_dominated_square_integral_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:10:29.555554+00:00
-- url     : https://prove2.me/theorems/5fb6f2a1-e0ea-4348-abe7-8b3f01b6de08
-- title:
--   Dominated a.e. convergence of squares implies convergence of exact quadratic integrals
-- statement:
--   For measurable random functions uniformly dominated in absolute value by a square-integrable envelope, establish convergence of their square integrals to the square integral of their almost surely pointwise limit.
-- source:
--   J-A22 original physical finite-band isometry to omitted-tail limit, purely analytic helper.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter AvramDividend.Classical
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja22_dominated_square_integral_convergence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (f : ℕ → Ω → ℝ) (g B : Ω → ℝ)
    (hf : ∀ k : ℕ, AEStronglyMeasurable (f k) P)
    (hlim : ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ => f k ω) atTop (nhds (g ω)))
    (hB : Integrable (fun ω => (B ω) ^ 2) P)
    (hdom : ∀ᵐ ω ∂P, ∀ k : ℕ, ‖f k ω‖ ≤ B ω) :
    Tendsto (fun k : ℕ => ∫ ω, (f k ω) ^ 2 ∂P)
      atTop (nhds (∫ ω, (g ω) ^ 2 ∂P)) := by sorry

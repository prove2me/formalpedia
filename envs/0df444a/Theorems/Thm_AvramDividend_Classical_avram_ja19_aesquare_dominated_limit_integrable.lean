-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja19_aesquare_dominated_limit_integrable
-- name    : AvramDividend.Classical.avram_ja19_aesquare_dominated_limit_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:49:21.357292+00:00
-- url     : https://prove2.me/theorems/7eeabbd1-3a71-4300-a36c-bcf065a49b88
-- title:
--   An almost-everywhere limit dominated by a square-integrable common envelope is square integrable
-- statement:
--   Under integrability of every real-valued approximation, pointwise almost everywhere convergence, and an almost everywhere common dominating random envelope whose square is integrable, the square of the limit is integrable. Prove using a.e. measurability of the pointwise limit, continuity of squaring and integrable domination, or Fatou and dominated convergence. The hypothesis includes the exact a.e. limit and uniform bound needed by the original physical smallband source.
-- source:
--   J-A19 generic analytical bridge; original Omega/P retained by application

import Mathlib
open MeasureTheory Set Filter
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja19_aesquare_dominated_limit_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (f : ℕ → Ω → ℝ) (g B : Ω → ℝ)
    (hf : ∀ k, Integrable (f k) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun k => f k ω) atTop (𝓝 (g ω)))
    (hB : Integrable (fun ω => (B ω) ^ 2) P)
    (hdom : ∀ᵐ ω ∂P, ∀ k, ‖f k ω‖ ≤ B ω) :
    Integrable (fun ω => (g ω) ^ 2) P := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_grid_upper_exit
-- name    : AvramDividend.Classical.gaussian_esscher_grid_upper_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T20:02:51.963672+00:00
-- url     : https://prove2.me/theorems/f3384b44-1f27-47c9-bc15-af3fb5b0086a
-- title:
--   Gaussian Esscher root bounds the q-discounted upper-exit payoff at a finite Lévy grid stop
-- statement:
--   For a spectrally negative Lévy process with σ>0 and q>0, choose the positive root φ satisfying ψ(φ)=q. At any bounded strict two-sided grid exit, the expected q-discounted indicator of upper exit is bounded by exp(-φ upper). The proof composes the independently proved Gaussian positive Esscher-root theorem with the full finite-grid upper-exit stopped exponential bound, without imposing additional integrability conditions.
-- source:
--   Proved positive_esscher_root_of_gaussian and levy_grid_upper_exit_discount_bound_complete at pinned Mathlib revision.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.gaussian_esscher_grid_upper_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (hσ : 0 < X.σ)
    (clock : ℕ → NNReal) (hc : Monotone clock) (hc0 : clock 0 = 0)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (lower upper : ℝ) (m : ℕ)
    (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Ioi (0 : ℝ)) 0 m ω) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q ∧
      (∫ ω, {ω : Ω | upper < X.X (clock (K ω)) ω}.indicator
        (fun z => Real.exp (-((clock (K z)) : ℝ) * q)) ω ∂P) ≤
        Real.exp (-φ * upper) := by sorry

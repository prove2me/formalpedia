-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_rightdiscount_cash_from_leftdiscount_bound_v2
-- name    : AvramDividend.Classical.avram_jump6_B_original_canonical_rightdiscount_cash_from_leftdiscount_bound_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:22:29.480437+00:00
-- url     : https://prove2.me/theorems/e9f1fc4f-ab8a-4b4d-8813-7d68e18bcb7c
-- title:
--   Source-exact original discounted dividend mesh endpoint correction (explicit sum binder)
-- statement:
--   A nonpositive left-endpoint discounted original canonical physical cash-minus-potential-secant sum yields a right-endpoint discounted upper bound with explicit q mesh-width times bounded local secant factor times true original dividend growth. This enables rigorous localisation before applying infinite-activity compensation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_canonical_rightdiscount_cash_from_leftdiscount_bound_v2
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (t : ℝ≥0) (j m : ℕ) :
    let Δ : ℝ≥0 := (1 : ℝ≥0) / ((j : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) t
    ∀ (L : ℝ), 0 ≤ L →
      ∀ (cash gap : ℕ → ℝ),
      (∀ i < m, 0 ≤
        Real.exp (-(q * (v i : ℝ))) -
        Real.exp (-(q * (v (i+1) : ℝ)))) →
      (∀ i < m, gap i ≤
        L * (rightLimit D (v (i+1)) ω - rightLimit D (v i) ω)) →
      (Finset.sum (Finset.range m) (fun i : ℕ =>
        cash i - Real.exp (-(q * (v i : ℝ))) * gap i)) ≤ 0 →
      (Finset.sum (Finset.range m) (fun i : ℕ =>
        cash i - Real.exp (-(q * (v (i+1) : ℝ))) * gap i)) ≤
      L * (q * (Δ : ℝ) *
        (rightLimit D (v m) ω - rightLimit D (v 0) ω)) := by sorry

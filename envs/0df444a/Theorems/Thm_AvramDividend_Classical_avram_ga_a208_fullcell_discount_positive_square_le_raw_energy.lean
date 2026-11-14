-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a208_fullcell_discount_positive_square_le_raw_energy
-- name    : AvramDividend.Classical.avram_ga_a208_fullcell_discount_positive_square_le_raw_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T21:06:40.729044+00:00
-- url     : https://prove2.me/theorems/6956d044-4dfb-48ee-b969-66ad838c1279
-- title:
--   Original stopped Gaussian positive discount square bounded by raw source squared energy
-- statement:
--   Finite physical full-cell source positive discount error has a quadratic-energy bound from the already Proved Cauchy grid estimate and the stopped finite-cell discount majorant. Supports the source-specific alternative to unrestricted a151.
-- source:
--   Proved Gaussian a154 and public a203

import Mathlib

theorem AvramDividend.Classical.avram_ga_a208_fullcell_discount_positive_square_le_raw_energy
 (m : ℕ) (A : ℕ → Prop) [DecidablePred A]
 (a u v R : ℕ → ℝ) (q Δ L : ℝ)
 (hq : 0 ≤ q) (hΔ : 0 ≤ Δ) (hL : 0 ≤ L)
 (hDisc : ∀ i ∈ Finset.range m, -(q*Δ) ≤ a i ∧ a i ≤ 0)
 (hLip : ∀ i ∈ Finset.range m, |u i - v i| ≤ L*|R i|) :
 (max (∑ i ∈ Finset.range m, if A i then a i*(u i-v i) else 0) 0)^2 ≤
   (q*Δ*L)^2 * (m : ℝ) * ∑ i ∈ Finset.range m, (if A i then R i else 0)^2 := by sorry

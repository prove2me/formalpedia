-- Prove2me | solution 1 for moustache_value_bound_mass
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T21:05:04.488768+00:00
-- url     : https://prove2.me/submissions/3ff5d509-9e0f-4c20-bf42-c98b655b2e0c

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.Monotone.Basic

set_option autoImplicit false
open MeasureTheory

theorem solution
    (G : ℝ → ℝ) (μ c : ℝ) (hμ : 0 < μ) (hc0 : 0 ≤ c) (hcμ : c < μ)
    (hleft : AntitoneOn G (Set.Icc 0 c))
    (hright : MonotoneOn G (Set.Icc c μ))
    (hsym : ∀ x, G (2 * μ - x) = G x)
    (hG0 : G 0 ≤ (1/2 : ℝ))
    (hint : IntervalIntegrable G volume 0 (2 * μ))
    (havg : (1 / 2 : ℝ) ≤ (1 / (2 * μ)) * ∫ x in (0:ℝ)..(2 * μ), G x) :
    (1 / 2 : ℝ) ≤ G μ := by
  have hcμ' : c ≤ μ := le_of_lt hcμ
  have h2μ : (0:ℝ) ≤ 2 * μ := by positivity
  have hμle : μ ≤ 2 * μ := by linarith
  have hsub01 : Set.uIcc (0:ℝ) μ ⊆ Set.uIcc 0 (2 * μ) := by
    rw [Set.uIcc_of_le (le_of_lt hμ), Set.uIcc_of_le h2μ]; exact Set.Icc_subset_Icc (le_refl 0) hμle
  have hsub12 : Set.uIcc (μ:ℝ) (2 * μ) ⊆ Set.uIcc 0 (2 * μ) := by
    rw [Set.uIcc_of_le hμle, Set.uIcc_of_le h2μ]; exact Set.Icc_subset_Icc (le_of_lt hμ) (le_refl _)
  have hint01 : IntervalIntegrable G volume 0 μ := hint.mono_set hsub01
  have hint12 : IntervalIntegrable G volume μ (2 * μ) := hint.mono_set hsub12
  have hrefl : (∫ x in (μ)..(2*μ), G x) = ∫ x in (0:ℝ)..μ, G x := by
    have hcg : (∫ x in (μ)..(2*μ), G x) = ∫ x in (μ)..(2*μ), G (2 * μ - x) := by
      apply intervalIntegral.integral_congr; intro x _; exact (hsym x).symm
    rw [hcg, intervalIntegral.integral_comp_sub_left G (2 * μ)]
    rw [show (2 * μ - μ) = μ by ring, show (2 * μ - 2 * μ) = (0:ℝ) by ring]
  have hsplit : (∫ x in (0:ℝ)..(2*μ), G x) = 2 * ∫ x in (0:ℝ)..μ, G x := by
    have := intervalIntegral.integral_add_adjacent_intervals hint01 hint12
    rw [← this, hrefl]; ring
  rw [hsplit] at havg
  have hμpos2 : (0:ℝ) < 2 * μ := by positivity
  have hμhalf : μ / 2 ≤ ∫ x in (0:ℝ)..μ, G x := by
    set I := ∫ x in (0:ℝ)..μ, G x with hI
    have hx : (1 / (2 * μ)) * (2 * I) = (1/μ) * I := by field_simp
    rw [hx] at havg
    have hμI : μ * (1/2) ≤ μ * ((1/μ) * I) := by
      apply mul_le_mul_of_nonneg_left havg (le_of_lt hμ)
    rw [show μ * ((1/μ) * I) = I by field_simp] at hμI
    linarith [hμI]
  have hGc_le_half : ∀ x ∈ Set.Icc (0:ℝ) c, G x ≤ (1/2 : ℝ) := by
    intro x hx; exact le_trans (hleft ⟨le_refl 0, hc0⟩ hx hx.1) hG0
  have hGc_le_Gμ : ∀ x ∈ Set.Icc c μ, G x ≤ G μ := by
    intro x hx; exact hright hx ⟨hcμ', le_refl μ⟩ hx.2
  have hsub0c : Set.uIcc (0:ℝ) c ⊆ Set.uIcc 0 μ := by
    rw [Set.uIcc_of_le hc0, Set.uIcc_of_le (le_of_lt hμ)]; exact Set.Icc_subset_Icc (le_refl 0) hcμ'
  have hsubcμ : Set.uIcc c μ ⊆ Set.uIcc 0 μ := by
    rw [Set.uIcc_of_le hcμ', Set.uIcc_of_le (le_of_lt hμ)]; exact Set.Icc_subset_Icc hc0 (le_refl μ)
  have hint0c : IntervalIntegrable G volume 0 c := hint01.mono_set hsub0c
  have hintcμ : IntervalIntegrable G volume c μ := hint01.mono_set hsubcμ
  have hb1 : (∫ x in (0:ℝ)..c, G x) ≤ ∫ _ in (0:ℝ)..c, (1/2 : ℝ) :=
    intervalIntegral.integral_mono_on hc0 hint0c intervalIntegrable_const hGc_le_half
  have hb2 : (∫ x in (c)..μ, G x) ≤ ∫ _ in (c)..μ, G μ :=
    intervalIntegral.integral_mono_on hcμ' hintcμ intervalIntegrable_const hGc_le_Gμ
  rw [intervalIntegral.integral_const] at hb1 hb2
  simp only [smul_eq_mul] at hb1 hb2
  have hadd : (∫ x in (0:ℝ)..μ, G x) = (∫ x in (0:ℝ)..c, G x) + ∫ x in (c)..μ, G x :=
    (intervalIntegral.integral_add_adjacent_intervals hint0c hintcμ).symm
  have hcomb : μ / 2 ≤ (c - 0) * (1/2) + (μ - c) * G μ := by
    have := hμhalf; rw [hadd] at this; linarith [hb1, hb2]
  have hpos : (0:ℝ) < μ - c := by linarith
  nlinarith [hcomb, hpos, mul_pos hpos hpos]

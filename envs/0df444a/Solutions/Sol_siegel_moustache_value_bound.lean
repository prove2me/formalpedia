-- Prove2me | solution 1 for siegel_moustache_value_bound
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T17:44:23.338605+00:00
-- url     : https://prove2.me/submissions/9ab313da-b26a-4ae0-8a5c-f5976a1516f8

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.Monotone.Basic

set_option autoImplicit false

open MeasureTheory

theorem solution
    (G : ℝ → ℝ) (μ c : ℝ) (hμ : 0 < μ) (hc0 : 0 ≤ c) (hcμ : c ≤ μ)
    (hleft : AntitoneOn G (Set.Icc 0 c))
    (hright : MonotoneOn G (Set.Icc c μ))
    (hsym : ∀ x, G (2 * μ - x) = G x)
    (h0μ : G 0 ≤ G μ)
    (hint : IntervalIntegrable G volume 0 (2 * μ))
    (havg : (1 / 2 : ℝ) ≤ (1 / (2 * μ)) * ∫ x in (0:ℝ)..(2 * μ), G x) :
    (1 / 2 : ℝ) ≤ G μ := by
  -- Step 1: on `[0, μ]`, `G x ≤ G μ` (unimodal max at endpoint, using `G 0 ≤ G μ`).
  have hpt : ∀ x ∈ Set.Icc (0:ℝ) μ, G x ≤ G μ := by
    intro x hx
    obtain ⟨hxa, hxb⟩ := hx
    rcases lt_or_ge x c with hxc | hcx
    · have hle : G x ≤ G 0 := hleft ⟨le_refl 0, hc0⟩ ⟨hxa, le_of_lt hxc⟩ hxa
      exact le_trans hle h0μ
    · exact hright ⟨hcx, hxb⟩ ⟨hcμ, le_refl μ⟩ hxb
  have h2μ : (0:ℝ) ≤ 2 * μ := by positivity
  have hμle : μ ≤ 2 * μ := by linarith
  -- integrability on the two halves
  have hsub01 : Set.uIcc (0:ℝ) μ ⊆ Set.uIcc 0 (2 * μ) := by
    rw [Set.uIcc_of_le (le_of_lt hμ), Set.uIcc_of_le h2μ]
    exact Set.Icc_subset_Icc (le_refl 0) hμle
  have hsub12 : Set.uIcc (μ:ℝ) (2 * μ) ⊆ Set.uIcc 0 (2 * μ) := by
    rw [Set.uIcc_of_le hμle, Set.uIcc_of_le h2μ]
    exact Set.Icc_subset_Icc (le_of_lt hμ) (le_refl _)
  have hint01 : IntervalIntegrable G volume 0 μ := hint.mono_set hsub01
  have hint12 : IntervalIntegrable G volume μ (2 * μ) := hint.mono_set hsub12
  -- Step 2: by symmetry, `∫_μ^{2μ} G = ∫_0^μ G`, hence `∫_0^{2μ} G = 2 ∫_0^μ G`.
  have hrefl : (∫ x in (μ)..(2*μ), G x) = ∫ x in (0:ℝ)..μ, G x := by
    have hcg : (∫ x in (μ)..(2*μ), G x) = ∫ x in (μ)..(2*μ), G (2 * μ - x) := by
      apply intervalIntegral.integral_congr
      intro x _; exact (hsym x).symm
    rw [hcg, intervalIntegral.integral_comp_sub_left G (2 * μ)]
    have : (2 * μ - μ) = μ := by ring
    rw [this]
    have h2 : (2 * μ - 2 * μ) = (0:ℝ) := by ring
    rw [h2]
  have hsplit : (∫ x in (0:ℝ)..(2*μ), G x) = 2 * ∫ x in (0:ℝ)..μ, G x := by
    have := intervalIntegral.integral_add_adjacent_intervals hint01 hint12
    rw [← this, hrefl]; ring
  -- Step 3: `∫_0^μ G ≤ ∫_0^μ (G μ) = μ * G μ`.
  have hbound : (∫ x in (0:ℝ)..μ, G x) ≤ μ * G μ := by
    have hmono : (∫ x in (0:ℝ)..μ, G x) ≤ ∫ _ in (0:ℝ)..μ, G μ :=
      intervalIntegral.integral_mono_on (le_of_lt hμ) hint01
        intervalIntegrable_const hpt
    rwa [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
  -- Step 4: combine.  avg = (1/(2μ))·(2∫_0^μ G) = (1/μ)∫_0^μ G ≤ G μ.
  rw [hsplit] at havg
  have hμpos : (0:ℝ) < 2 * μ := by positivity
  have h2 : (1 / 2 : ℝ) ≤ (1 / μ) * ∫ x in (0:ℝ)..μ, G x := by
    have hne : μ ≠ 0 := ne_of_gt hμ
    have : (1 / (2 * μ)) * (2 * ∫ x in (0:ℝ)..μ, G x)
         = (1 / μ) * ∫ x in (0:ℝ)..μ, G x := by
      field_simp
    rwa [this] at havg
  -- (1/μ)∫_0^μ G ≤ G μ  from  ∫_0^μ G ≤ μ G μ
  have h3 : (1 / μ) * ∫ x in (0:ℝ)..μ, G x ≤ G μ := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hμ]
    linarith [hbound]
  linarith

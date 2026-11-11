-- Prove2me | solution 1 for ja18_anoise46_direct_copy_disj_ff94d009
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T19:12:57.850599+00:00
-- url     : https://prove2.me/submissions/2985aa45-c85d-4626-9384-ad8a83d4f46d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_anoise34_dyadic_mark_cell_endpoint_error
import Theorems.Thm_AvramDividend_Classical_avram_anoise43_unit_dyadic_halfopen_cover
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
theorem solution
    {α : Type*} [DecidableEq α] (n : ℕ) (F : Finset α)
    (j : α → ℝ)
    (hF : ∀ u ∈ F, j u ∈ Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))) 
    : (let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))); let C : ℕ → ℕ → Set ℝ := (fun k i => B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k) (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)); (∀ (k i l : ℕ) (hil : i ≠ l), Disjoint (C k i) (C k l))) := by
    classical
    let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
    let C : ℕ → ℕ → Set ℝ := fun k i =>
        B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
          (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
    let w : ℕ → ℕ → ℝ := fun k i => -1 + (i : ℝ) / (2 : ℝ) ^ k
    let q : ℕ → ℝ := fun k =>
        ∑ i ∈ Finset.range (2 ^ k), w k i * ((F.filter (fun u => j u ∈ C k i)).card : ℝ)
    let I : ℝ := ∑ u ∈ F, j u
    let e : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k * (F.card : ℝ)
    change ∀ (k i l : ℕ) (hil : i ≠ l), Disjoint (C k i) (C k l)
    intro k i l hil
    have hsub (a : ℕ) : C k a ⊆
        Ioc (-1 + (a : ℝ) / (2 : ℝ) ^ k)
          (-1 + ((a : ℝ) + 1) / (2 : ℝ) ^ k) := by
      intro z hz
      exact hz.2
    rcases lt_or_gt_of_ne hil with hlt | hgt
    · have hq : ((i : ℝ) + 1) / (2 : ℝ) ^ k ≤
          (l : ℝ) / (2 : ℝ) ^ k := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast Nat.succ_le_of_lt hlt
        · positivity
      exact (Set.Ioc_disjoint_Ioc_of_le (add_le_add_right hq (-1))).mono
        (hsub i) (hsub l)
    · have hq : ((l : ℝ) + 1) / (2 : ℝ) ^ k ≤
          (i : ℝ) / (2 : ℝ) ^ k := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast Nat.succ_le_of_lt hgt
        · positivity
      exact ((Set.Ioc_disjoint_Ioc_of_le (add_le_add_right hq (-1))).mono
        (hsub l) (hsub i)).symm
end

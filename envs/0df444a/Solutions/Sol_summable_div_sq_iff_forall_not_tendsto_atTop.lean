-- Prove2me | solution 1 for summable_div_sq_iff_forall_not_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:34:13.851479+00:00
-- url     : https://prove2.me/submissions/70ed6368-47e1-4fcc-951d-fffa3fc03be6

module
public import Definitions.Def_Fekete_DeBruijnErdos
public import Definitions.Def_Fekete_Sharpness
public import Theorems.Thm_NearlySubadditive_witness_le_add
public import Theorems.Thm_NearlySubadditive_tendsto_witness_div
public import Theorems.Thm_NearlySubadditive_of_le_add
public import Theorems.Thm_NearlySubadditive_tendsto_atBot_or_exists_tendsto_of_summable


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Finset
open scoped Topology
open NearlySubadditive
theorem _root_.solution (hf0 : 0 ≤ f) (hf : Monotone f) :
    (Summable fun n : ℕ ↦ f n / (n : ℝ) ^ 2) ↔
      ∀ u : ℕ → ℝ, (∀ m n, u (m + n) ≤ u m + u n + f (m + n)) →
        ¬ Tendsto (fun n ↦ u n / n) atTop atTop := by
  refine ⟨fun hfs u hu htop ↦ ?_, fun H ↦ ?_⟩
  · have h : NearlySubadditive f 2 0 u := .of_le_add fun m n _ _ ↦ hu m n
    rcases h.tendsto_atBot_or_exists_tendsto_of_summable one_lt_two hf hfs with hbot | ⟨L, hL⟩
    · exact hbot.not_tendsto disjoint_atBot_atTop htop
    · exact not_tendsto_atTop_of_tendsto_nhds hL htop
  · by_contra hfs
    exact H _ (witness_le_add hf0 hf)
      (tendsto_witness_div hf0 hfs)

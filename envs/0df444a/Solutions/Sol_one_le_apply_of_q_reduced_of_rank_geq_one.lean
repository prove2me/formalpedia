-- Prove2me | solution 1 for one_le_apply_of_q_reduced_of_rank_geq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:51:15.895434+00:00
-- url     : https://prove2.me/submissions/849d3bf8-f90d-4fe1-9bf7-e1efc826883d

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Rank
public import Theorems.Thm_rank_geq_iff
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_eff_one_chip
public import Theorems.Thm_effective_of_winnable_and_q_reduced
public import Theorems.Thm_legal_set_empty
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty



set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution {G : CFGraph} {q : G.V}
    {D : CFDiv G} (hred : q_reduced G q D) (hrank : rank G D ≥ 1) :
    1 ≤ D q := by
  classical
  have hval : ∀ v : G.V, v ≠ q → (D - one_chip q) v = D v := by
    intro v hv
    simp [Pi.sub_apply, one_chip_apply_other' q v hv]
  have hwin : winnable G (D - one_chip q) :=
    (rank_geq_iff G D 1).mpr hrank (one_chip q) ⟨eff_one_chip q, deg_one_chip q⟩
  have hred' : q_reduced G q (D - one_chip q) := by
    refine ⟨fun v hv => by rw [hval v hv]; exact hred.1 v hv, ?_⟩
    intro S hq hSne hlegal
    apply hred.2 S hq hSne
    intro v hvS
    rw [← hval v (fun hvq => hq (hvq ▸ hvS))]
    exact hlegal v hvS
  have heff : effective (D - one_chip q) :=
    effective_of_winnable_and_q_reduced G q _ hwin hred'
  have hq := heff q
  simp only [Pi.sub_apply, one_chip_apply_v] at hq
  omega

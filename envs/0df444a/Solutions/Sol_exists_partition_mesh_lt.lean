-- Prove2me | solution 1 for exists_partition_mesh_lt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:52:51.151577+00:00
-- url     : https://prove2.me/submissions/43723105-25df-4a09-b5ba-5543462b57cd

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators Pointwise
noncomputable section
section RS_integral_uniqueness

theorem solution {a b δ : ℝ} (hab : a < b) (hδ : 0 < δ) :
    ∃ P : Partition a b, P.mesh < δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / δ)
  let N := n + 1
  have hNpos : 0 < N := Nat.succ_pos n
  refine ⟨uniformPartition a b hab N hNpos, ?_⟩
  rw [uniformPartition_mesh_eq]
  have hNposR : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hltN : (b - a) / δ < (N : ℝ) := by
    have hnle : (n : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_succ_self n
    exact lt_trans hn hnle
  have hmul : b - a < (N : ℝ) * δ := by
    rwa [div_lt_iff₀ hδ] at hltN
  rw [div_lt_iff₀ hNposR]
  nlinarith
end RS_integral_uniqueness

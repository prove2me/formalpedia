-- Prove2me | solution 1 for mme_dwz_table2_integral_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T10:21:57.304277+00:00
-- url     : https://prove2.me/submissions/64d7f143-cc1f-41e6-95dd-7c5baba4050e

import Definitions.Def_mme_dwz_square_data

open MME.DWZSquare

set_option maxRecDepth 100000

/-!
The explicit period `10^16` clears both the denominator `10^8` of every
Table 2 component weight and the denominator `10^8` of every nontrivial
restricted Z-split.  The theorem states only the two exact cardinalities used
to form type classes in the level-2 analysis.
-/

private def table2AlphaNumerator : Fin 15 → ℕ :=
  ![20860, 24731, 24731,
    1211153, 1333318, 1211153, 1251758, 1333318, 1251758,
    10366945, 10366945, 10045791,
    20088623, 20734458, 20734458]

private def table2SplitNumerator : Fin 15 → Fin 3 → ℕ := fun s ↦
  if s = 9 ∨ s = 10 then
    ![3477403, 93045194, 3477403]
  else if s = 12 then
    ![21015, 99957970, 21015]
  else if shapeZ s = 0 then
    ![100000000, 0, 0]
  else if shapeZ s = 1 then
    ![50000000, 50000000, 0]
  else if shapeZ s = 3 then
    ![0, 50000000, 50000000]
  else
    ![0, 0, 100000000]

private theorem table2_alpha_denominator (s : Fin 15) :
    (100000000 : ℝ) * alpha s = table2AlphaNumerator s := by
  fin_cases s <;>
    simp [table2AlphaNumerator, alpha] <;>
    norm_num

private theorem table2_split_denominator (s : Fin 15) (r : Fin 3) :
    (100000000 : ℝ) * zSplit s r = table2SplitNumerator s r := by
  fin_cases s <;> fin_cases r <;>
    simp [table2SplitNumerator, zSplit, shapeZ, splitA, splitB] <;>
    norm_num

private theorem table2_joint_denominator (s : Fin 15) (r : Fin 3) :
    (10000000000000000 : ℝ) * alpha s * zSplit s r =
      (table2AlphaNumerator s * table2SplitNumerator s r : ℕ) := by
  rw [Nat.cast_mul]
  calc
    (10000000000000000 : ℝ) * alpha s * zSplit s r =
        ((100000000 : ℝ) * alpha s) *
          ((100000000 : ℝ) * zSplit s r) := by ring
    _ = (table2AlphaNumerator s : ℝ) * table2SplitNumerator s r := by
      rw [table2_alpha_denominator, table2_split_denominator]

theorem solution (N₀ : ℕ) :
    ∃ N : ℕ, N₀ < N ∧
      (∀ s : Fin 15, ∃ componentCount : ℕ,
        (N : ℝ) * alpha s = componentCount) ∧
      (∀ s : Fin 15, ∀ r : Fin 3, ∃ splitCount : ℕ,
        (N : ℝ) * alpha s * zSplit s r = splitCount) := by
  let period : ℕ := 10000000000000000
  refine ⟨period * (N₀ + 1), ?_, ?_, ?_⟩
  · dsimp [period]
    omega
  · intro s
    refine ⟨100000000 * table2AlphaNumerator s * (N₀ + 1), ?_⟩
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    calc
      (period : ℝ) * (N₀ + 1) * alpha s =
          ((100000000 : ℝ) * alpha s) *
            (100000000 * (N₀ + 1)) := by
              dsimp [period]
              ring
      _ = (table2AlphaNumerator s : ℝ) *
            (100000000 * (N₀ + 1)) := by
              rw [table2_alpha_denominator]
      _ = ↑(100000000 * table2AlphaNumerator s * (N₀ + 1)) := by
              norm_num
              ring
  · intro s r
    refine ⟨(table2AlphaNumerator s * table2SplitNumerator s r) *
      (N₀ + 1), ?_⟩
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    calc
      (period : ℝ) * (N₀ + 1) * alpha s * zSplit s r =
          ((period : ℝ) * alpha s * zSplit s r) * (N₀ + 1) := by ring
      _ = (table2AlphaNumerator s * table2SplitNumerator s r : ℕ) *
            (N₀ + 1) := by
              dsimp [period]
              rw [table2_joint_denominator]
      _ = ↑((table2AlphaNumerator s * table2SplitNumerator s r) *
            (N₀ + 1)) := by norm_num

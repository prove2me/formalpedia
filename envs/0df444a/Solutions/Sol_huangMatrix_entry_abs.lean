-- Prove2me | solution 1 for huangMatrix_entry_abs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-04-23T04:04:42.529882+00:00
-- url     : https://prove2.me/submissions/2e528dd4-fe3c-4bf7-b6a3-659c1cc90d5b

import Definitions.Def_Hypercube
import Definitions.Def_huangMatrix
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Cases

/-!
# huangMatrix entry absolute value

The entries of `huangMatrix n` are ±1 on edges of the hypercube and 0 elsewhere.
Equivalently: `|A_n[u,v]| = 1 if u ~ v in Q_n, else 0`. Ties the algebraic matrix
to the combinatorial graph structure — needed whenever we bridge `huangMatrix`
with `Hypercube.Adj` (e.g. when applying the generic spectral-graph bound
`max_degree_ge_lambda_max` to a principal submatrix of `huangMatrix`).
-/


/-!
# Full proof — huangMatrix_entry_abs

A direct proof of `huangMatrix_entry_abs`, no grand-children. Two steps:
1. Show every entry of `huangMatrix n` is in `{0, 1, -1}` (induction on `n`
   using the block-matrix recursive structure).
2. Show an entry is nonzero iff the indices differ in exactly one coordinate
   (induction on `n`, unfolding the block structure).
Combining gives the absolute-value characterization.
-/

theorem solution :
    ∀ (n : ℕ) (u v : Fin n → Bool),
      |huangMatrix n u v| = if Hypercube.Adj n u v then 1 else 0 := by
  intro n u v
  have h_hu_finite : ∀ n : ℕ, ∀ u v : Fin n → Bool,
      huangMatrix n u v = 0 ∨ huangMatrix n u v = 1 ∨ huangMatrix n u v = -1 := by
    intro n
    induction' n with n ih <;> simp_all +decide [huangMatrix]
    intro u v; rcases split n u with (u | u) <;> rcases split n v with (v | v) <;>
      simp +decide [*]
    · by_cases h : u = v <;> aesop
    · by_cases h : u = v <;> aesop
    · rcases ih u v with h | h | h <;> norm_num [h]
  have h_adj : ∀ n : ℕ, ∀ u v : Fin n → Bool,
      huangMatrix n u v ≠ 0 ↔ Hypercube.Adj n u v := by
    intro n; induction' n with n ih <;> simp_all +decide [Hypercube.Adj]
    · rfl
    · intro u v
      erw [show huangMatrix (n + 1) = Matrix.reindex (split n |> Equiv.symm)
            (split n |> Equiv.symm) (Matrix.fromBlocks (huangMatrix n)
            (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ)
            (1 : Matrix (Fin n → Bool) (Fin n → Bool) ℝ) (-huangMatrix n)) from rfl]
      simp +decide [Matrix.fromBlocks, split]
      split_ifs <;> simp_all +decide [Finset.card_eq_one]
      · constructor <;> rintro ⟨a, ha⟩
        · use Fin.succ a
          ext i; induction i using Fin.inductionOn <;> simp_all +decide [Finset.ext_iff]
          exact ne_of_lt (Fin.succ_pos _)
        · simp_all +decide [Finset.eq_singleton_iff_unique_mem]
          rcases a with ⟨_ | a, ha⟩ <;> simp_all +decide [Fin.forall_fin_succ]
          exact ⟨⟨a, by linarith⟩, ha.1, fun x hx => by
            simpa [Fin.ext_iff] using congr_arg Fin.val (ha.2 x hx)⟩
      · simp_all +decide [Finset.eq_singleton_iff_unique_mem, Matrix.one_apply]
        constructor <;> intro h <;> simp_all +decide [funext_iff, Fin.forall_fin_succ]
      · simp_all +decide [Finset.ext_iff, Matrix.one_apply]
        constructor <;> intro h <;> simp_all +decide [funext_iff, Fin.forall_fin_succ]
      · simp +decide [Finset.ext_iff]
        constructor <;> rintro ⟨a, ha⟩
        · use Fin.succ a
          intro i; induction i using Fin.inductionOn <;> simp_all +decide
          exact ne_of_lt (Fin.succ_pos _)
        · cases a using Fin.inductionOn <;> simp_all +decide [Fin.forall_fin_succ]
  specialize h_adj n u v; specialize h_hu_finite n u v; aesop

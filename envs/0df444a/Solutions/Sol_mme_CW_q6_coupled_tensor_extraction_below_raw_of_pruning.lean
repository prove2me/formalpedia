-- Prove2me | solution 1 for mme_CW_q6_coupled_tensor_extraction_below_raw_of_pruning
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T05:39:27.841082+00:00
-- url     : https://prove2.me/submissions/295bdca3-a443-4e2d-aa69-a60557effb37
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_mme_tensor_quotient
import Theorems.Thm_mme_CW_q6_coupled_hash_survivors_below_raw
import Theorems.Thm_mme_CW_q6_coupled_survivors_assemble_MM

open MME BigOperators Filter

universe u

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V < 4 * (6 : ℝ) ^ (3 * tau) *
        ((6 : ℝ) ^ (3 * tau) + 2)) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let G : ℕ := N - L
      (0 < L ∧ L + G = N ∧ 341 * L < 100 * G) →
      ∃ (k : ℕ) (a b c : Fin k → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
          ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N)) ∧
        V ^ (2 * N) ≤
          ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  have hhash := mme_CW_q6_coupled_hash_survivors_below_raw
    (K := K) tau htau V hV hVlt
  filter_upwards [hhash] with N hhash
  dsimp only at hhash ⊢
  intro hprune
  obtain ⟨k, hsurvivors, hcount⟩ := hhash hprune
  let L : ℕ := ⌊2 / ((6 : ℝ) ^ (3 * tau) + 2) * (N : ℝ)⌋₊
  let G : ℕ := N - L
  let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
  refine ⟨k, (fun _ => side), (fun _ => side), (fun _ => side), ?_, ?_⟩
  · exact TensorObj.Restrict.trans
      (mme_CW_q6_coupled_survivors_assemble_MM (K := K) L G k)
      (by simpa only [L, G] using hsurvivors)
  · calc
      V ^ (2 * N) ≤
          (k : ℝ) * (((side * side * side : ℕ) : ℝ) ^ tau) := by
        simpa only [L, G, side] using hcount
      _ = ∑ _i : Fin k,
          ((((fun _ : Fin k => side) _i) *
            ((fun _ : Fin k => side) _i) *
            ((fun _ : Fin k => side) _i) : ℕ) : ℝ) ^ tau := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]

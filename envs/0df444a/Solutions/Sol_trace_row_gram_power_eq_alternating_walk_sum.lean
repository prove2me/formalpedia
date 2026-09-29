-- Prove2me | solution 1 for trace_row_gram_power_eq_alternating_walk_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-24T01:39:24.96798+00:00
-- url     : https://prove2.me/submissions/c0f60ce2-5b08-4ab1-aa8d-449e31176374

import Theorems.Thm_trace_pow_eq_walk
import Definitions.Def_buchholz_signed_walk_sum

open MatrixCompletion
open scoped BigOperators

theorem solution
    (n : Nat) (hn : 1 ≤ n) {n1 n2 : Nat} (S : RealMatrix n1 n2) :
    Matrix.trace ((S * S.transpose) ^ n)
      =
    ∑ rows : Fin n → Fin n1,
      ∑ cols : Fin n → Fin n2,
        ∏ k : Fin n,
          S (rows k) (cols k) *
            S (rows (buchholzCyclicSucc k)) (cols k) := by
  classical
  cases n with
  | zero =>
      omega
  | succ m =>
      rw [trace_pow_eq_walk (M := S * S.transpose) m]
      apply Finset.sum_congr rfl
      intro rows _
      have hsucc :
          (fun k : Fin (m + 1) =>
              rows ⟨(k.1 + 1) % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩)
            =
          (fun k : Fin (m + 1) => rows (buchholzCyclicSucc k)) := by
        funext k
        congr 1
      calc
        (∏ k : Fin (m + 1),
          (S * S.transpose) (rows k)
            (rows ⟨(k.1 + 1) % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩))
            =
          ∏ k : Fin (m + 1),
            (S * S.transpose) (rows k) (rows (buchholzCyclicSucc k)) := by
            apply Finset.prod_congr rfl
            intro k _
            rw [congrFun hsucc k]
        _ =
          ∏ k : Fin (m + 1),
            ∑ j : Fin n2,
              S (rows k) j * S (rows (buchholzCyclicSucc k)) j := by
            apply Finset.prod_congr rfl
            intro k _
            simp [Matrix.mul_apply, Matrix.transpose_apply]
        _ =
          ∑ cols : Fin (m + 1) → Fin n2,
            ∏ k : Fin (m + 1),
              S (rows k) (cols k) *
                S (rows (buchholzCyclicSucc k)) (cols k) := by
            rw [Fintype.prod_sum]

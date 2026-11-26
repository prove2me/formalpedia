-- Prove2me | solution 1 for section5_embed_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:52:52.033132+00:00
-- url     : https://prove2.me/submissions/f53fce53-c58e-4138-af2c-e99b7e318636

import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Membership_gates12
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership
theorem solution {k n : ℕ} (v : Qubits k → ℂ) (w : Fin k ↪ Fin n) :
    embedOp (Matrix.diagonal v) w = Matrix.diagonal (fun z => v (z ∘ w)) := by
  classical
  ext y z
  by_cases h : y = z
  · subst z
    simp [embedOp, Matrix.diagonal_apply]
  · have hh : ¬ ((∀ j : Fin n, j ∉ Set.range w → y j = z j) ∧ y ∘ w = z ∘ w) := by
      rintro ⟨hr,hs⟩
      apply h
      funext j
      by_cases hj : j ∈ Set.range w
      · obtain ⟨i,rfl⟩ := hj
        exact congrFun hs i
      · exact hr j hj
    simp only [embedOp, Matrix.of_apply, Matrix.diagonal_apply, if_neg h]
    split_ifs with hr hs
    · exact False.elim (hh ⟨hr,hs⟩)
    · rfl
    · rfl

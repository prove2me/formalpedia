-- Prove2me | solution 1 for section5_rational_best_column_correct
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:00:25.630168+00:00
-- url     : https://prove2.me/submissions/2bdbf900-e772-45b7-a568-65bfe22ca48e

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5PowerColumnRecovery
import Definitions.Def_Section5Verified_Section5RationalReconstruction
import Mathlib
import Theorems.Thm_section5_rational_column_score
section
set_option autoImplicit false

open ContinuousLinearMap InnerProductSpace

/-! Computable rational-complex matrix powers and column selection, together with
their exact complex-operator semantics. No eigenvector oracle is used. -/





























theorem section5_max_index_fold_spec {I : Type*} (score : I → ℚ) (l : List I) (j : I) :
    score j ≤ score (section5_max_index_fold score l j) ∧
      ∀ i ∈ l, score i ≤ score (section5_max_index_fold score l j) := by
  induction l generalizing j with
  | nil => exact ⟨le_rfl,by simp⟩
  | cons i l ih =>
    change score j ≤ score (section5_max_index_fold score l (if score j < score i then i else j)) ∧
      ∀ k ∈ i::l, score k ≤ score (section5_max_index_fold score l (if score j < score i then i else j))
    by_cases h : score j < score i
    · have ht := ih i
      rw [if_pos h]
      refine ⟨h.le.trans ht.1,?_⟩
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact ht.1
      · exact ht.2 k hk
    · have ht := ih j
      rw [if_neg h]
      refine ⟨ht.1,?_⟩
      intro k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact (le_of_not_gt h).trans ht.1
      · exact ht.2 k hk















end
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace
theorem solution {n : ℕ} (A : Section5RationalMatrix n) (hn : 1 ≤ n) :
    ∀ i, ‖A.operator (section5_coordinate_ket i)‖ ≤
      ‖A.operator (section5_coordinate_ket (A.bestColumn hn))‖ := by
  intro i
  have hh := (section5_max_index_fold_spec A.columnScore (List.finRange n) ⟨0,by omega⟩).2 i
    (List.mem_finRange i)
  have hreal : (A.columnScore i:ℝ) ≤ (A.columnScore (A.bestColumn hn):ℝ) := by
    exact_mod_cast hh
  rw [← section5_rational_column_score,← section5_rational_column_score] at hreal
  nlinarith [norm_nonneg (A.operator (section5_coordinate_ket i)),
    norm_nonneg (A.operator (section5_coordinate_ket (A.bestColumn hn)))]

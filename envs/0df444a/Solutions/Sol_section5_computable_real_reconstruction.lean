-- Prove2me | solution 1 for section5_computable_real_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:16:54.858826+00:00
-- url     : https://prove2.me/submissions/189b819c-263c-41ef-bebf-10efb4f28f70

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
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Definitions.Def_Section5Verified_Section5PowerColumnRecovery
import Definitions.Def_Section5Verified_Section5QuantizedReconstruction
import Definitions.Def_Section5Verified_Section5RationalReconstruction
import Mathlib
import Theorems.Thm_section5_power_column_estimator
import Theorems.Thm_section5_rational_best_column_correct
import Theorems.Thm_section5_rational_power_operator
import Theorems.Thm_section5_rational_real_candidate
import Theorems.Thm_section5_unnormalized_real_recovery
section
set_option autoImplicit false

open ContinuousLinearMap InnerProductSpace

/-! Statistical operator error implies the real, sign-ambiguous direction guarantee
used by Theorem 5.6. This is the reconstruction guarantee; no efficient measurement
or classical eigenvector algorithm is assumed to have been constructed here. -/

theorem section5_complexify_norm {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) :
    ‖section5_complexify w‖=‖w‖ := by
  have hs : ‖section5_complexify w‖^2=‖w‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq,section5_complexify,WithLp.ofLp_toLp,
      Complex.norm_real]
  nlinarith [norm_nonneg w,norm_nonneg (section5_complexify w)]



end
section
set_option autoImplicit false

/-! Passing from a powered matrix column to its larger real/imaginary part needs
no square root in the algorithm. Normalization is used only in the guarantee. -/











theorem section5_power_real_reconstruction {n : ℕ} (hn : 1 ≤ n)
    (L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hL : IsSelfAdjoint L)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) (k : ℕ)
    (hprec : 400*(n:ℝ)/ε ≤ (2:ℝ)^(k+1))
    (j : Fin n) (hmax : ∀ i, ‖(L^(k+1)) (section5_coordinate_ket i)‖ ≤
      ‖(L^(k+1)) (section5_coordinate_ket j)‖)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1)
    (herror : ‖L-InnerProductSpace.rankOne ℂ (section5_complexify w) (section5_complexify w)‖ ≤ ε/1000) :
    let r := section5_larger_real_part ((L^(k+1)) (section5_coordinate_ket j))
    r ≠ 0 ∧ (‖NormedSpace.normalize r-w‖ ≤ ε/6 ∨ ‖NormedSpace.normalize r+w‖ ≤ ε/6) := by
  obtain ⟨hy,ζ,hζ,hclose⟩ := section5_power_column_estimator hn L hL ε hε hε' k hprec j hmax
    (section5_complexify w) (by rwa [section5_complexify_norm]) herror
  exact section5_unnormalized_real_recovery _ hy w hw ζ ε hε hε' hclose

end
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace
theorem solution {n : ℕ} (hn : 1 ≤ n)
    (A : Section5RationalMatrix n) (hA : IsSelfAdjoint A.operator)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) (k : ℕ)
    (hprec : 400*(n:ℝ)/ε ≤ (2:ℝ)^(k+1))
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1)
    (herror : ‖A.operator-rankOne ℂ (section5_complexify w) (section5_complexify w)‖ ≤ ε/1000) :
    let r : EuclideanSpace ℝ (Fin n) :=
      WithLp.toLp 2 (fun i => ((A.power (k+1)).realCandidate hn i:ℝ))
    r ≠ 0 ∧ (‖NormedSpace.normalize r-w‖ ≤ ε/6 ∨ ‖NormedSpace.normalize r+w‖ ≤ ε/6) := by
  dsimp only
  rw [section5_rational_real_candidate,section5_rational_power_operator]
  have hmax := section5_rational_best_column_correct (A.power (k+1)) hn
  rw [section5_rational_power_operator] at hmax
  exact section5_power_real_reconstruction hn A.operator hA ε hε hε' k hprec _ hmax w hw herror

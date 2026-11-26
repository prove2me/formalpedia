-- Prove2me | solution 1 for section5_scaled_integer_candidate_bounds
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T20:18:11.010781+00:00
-- url     : https://prove2.me/submissions/babf564a-e490-404c-892a-b321e99f3509

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
import Definitions.Def_Section5Verified_Section5IntegerMatrixBounds
import Definitions.Def_Section5Verified_Section5IntegerSpectralBridge
import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Definitions.Def_Section5Verified_Section5PowerColumnRecovery
import Definitions.Def_Section5Verified_Section5QuantizedReconstruction
import Mathlib
import Theorems.Thm_section5_dyadic_max_score_column
import Theorems.Thm_section5_integer_scaled_candidate
import Theorems.Thm_section5_power_column_magnitude_bounds
import Theorems.Thm_section5_scaled_power_output_bounds
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
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives ContinuousLinearMap InnerProductSpace
theorem solution {n : ℕ} (hn : 1 ≤ n)
    (A : Section5IntegerMatrix n) (q k : ℕ) (hA : IsSelfAdjoint (A.dyadicOperator q))
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖=1)
    (η : ℝ) (hη : 0 ≤ η) (hη' : η ≤ 1/1000)
    (herror : ‖A.dyadicOperator q-rankOne ℂ (section5_complexify w) (section5_complexify w)‖ ≤ η)
    (j : Fin n) (hmax : ∀ i, (A.power (k+1)).columnScore i ≤ (A.power (k+1)).columnScore j) :
    let r := ((2:ℝ)^((q+1)*(k+1)))⁻¹ •
      (WithLp.toLp 2 (fun i => ((A.power (k+1)).realCandidateAt j i:ℝ)))
    1/(3*n*(4:ℝ)^(k+1)) ≤ ‖r‖ ∧ ‖r‖ ≤ 1 := by
  dsimp only
  rw [section5_integer_scaled_candidate]
  obtain ⟨hlo,hhi⟩ := section5_power_column_magnitude_bounds hn (A.dyadicOperator q) hA
    (section5_complexify w) (by rwa [section5_complexify_norm]) η hη hη' herror k j
    (section5_dyadic_max_score_column A q (k+1) j hmax)
  exact section5_scaled_power_output_bounds hn _ (k+1) hlo hhi

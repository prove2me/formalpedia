-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_cokernel_finite_card_eq_inv_modulus
-- name    : Formalism.FourierDecayAlt.P.A5x5.cokernel_finite_card_eq_inv_modulus
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:26:28.890808+00:00
-- url     : https://prove2.me/theorems/59aa4c3b-22aa-4c38-8bef-376543f6f7de
-- title:
--   A5x5: cokernel finite card eq inv modulus
-- statement:
--   The A5x5 construction uses the cokernel finite card eq inv modulus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelNonzeroModulusDeterminantEq.lean#L725-L765
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelNonzeroModulusDeterminantEq.lean#L725-L765

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x5
variable {K : Type} [CommRing K]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {R : Subring K}
variable [TopologicalSpace K] [IsTopologicalRing K] {ψ : AddChar K ℂ}

theorem Formalism.FourierDecayAlt.P.A5x5.cokernel_finite_card_eq_inv_modulus (hd : LocalDatum K R ψ) (n : ℕ) (Z : Matrix (Fin n) (Fin n) K)
    (hZ : IsInt R Z) (hdet : IsUnit Z.det) :
    Finite (coker R Z) ∧ (Nat.card (coker R Z) : ℝ) = (modK R Z.det)⁻¹ := by sorry

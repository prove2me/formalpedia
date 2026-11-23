-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_mem_isoZZ_iff
-- name    : Formalism.FourierDecayAlt.P.A5x6.mem_isoZZ_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:12.339775+00:00
-- url     : https://prove2.me/theorems/a960a5d8-d4b3-49e4-bf00-da2d8e167ec2
-- title:
--   A5x6: mem iso ZZ iff
-- statement:
--   The A5x6 construction uses the mem iso ZZ iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelPropertiesOfHypotheses.lean#L275-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstKernelPropertiesOfHypotheses.lean#L275-L288

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x6
variable {K : Type} [CommRing K] (R : Subring K)

theorem Formalism.FourierDecayAlt.P.A5x6.mem_isoZZ_iff {n n' : ℕ} (Z : Matrix (Fin n) (Fin n) K) (Z' : Matrix (Fin n') (Fin n') K)
    (hZ : IsUnit Z.det) (hZ' : IsUnit Z'.det) (θ : coker R Z ≃ₗ[R] coker R Z') :
    θ ∈ isoZZ R Z Z' ↔ eZ R Z - θ.symm (eZ R Z') = 0 ∧
      muZ R Z hZ - (muZ R Z' hZ').comp θ.toLinearMap = 0 := by sorry

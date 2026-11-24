-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_block3_middle_contDiffOn
-- name    : Formalism.FourierDecayAlt.P.Ux10.block3_middle_contDiffOn
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:42:43.824726+00:00
-- url     : https://prove2.me/theorems/fa583c8e-853e-409f-b5d4-a9be0d5d594a
-- title:
--   Ux10: block3 middle cont Diff On
-- statement:
--   The Ux10 construction uses the block3 middle cont Diff On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhiBoundPartsOfRadicalParametrisation.lean#L1168-L1185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhiBoundPartsOfRadicalParametrisation.lean#L1168-L1185

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyTransformPreservesForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
open MeasureTheory Filter Topology
open Matrix Filter Topology
open Matrix MeasureTheory Filter Topology
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux10
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.Ux10.block3_middle_contDiffOn {k j ρ : ℕ} (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ)
    (A13 : Matrix (Fin j) (Fin j) ℂ) (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A31 : Matrix (Fin j) (Fin j) ℂ)
    (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun γ : B.Mat k ρ => blk3 (k := k) (j := j) (ρ := ρ) A11 A12 A13 A21 γ A23 A31 A32 A33) Set.univ := by sorry

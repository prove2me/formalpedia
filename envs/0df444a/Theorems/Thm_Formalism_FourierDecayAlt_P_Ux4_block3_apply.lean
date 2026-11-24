-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block3_apply
-- name    : Formalism.FourierDecayAlt.P.Ux4.block3_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:47:35.010738+00:00
-- url     : https://prove2.me/theorems/b92780ee-149e-4a2a-8ff9-985877d6a324
-- title:
--   Ux4: block3 apply
-- statement:
--   The Ux4 construction uses the block3 apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L21-L28

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux4
variable {k j ρ : ℕ}

theorem Formalism.FourierDecayAlt.P.Ux4.block3_apply
    (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ)
    (x y : Ix k j ρ) :
    blk3 A11 A12 A13 A21 A22 A23 A31 A32 A33 (eB k j ρ x) (eB k j ρ y) =
      Matrix.fromBlocks (Matrix.fromBlocks A11 A12 A21 A22) (Matrix.fromRows A13 A23) (Matrix.fromCols A31 A32) A33 x y := by sorry

-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_rn_of
-- name    : Formalism.FourierDecayAlt.P.Ux3.rn_of
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:26:18.609896+00:00
-- url     : https://prove2.me/theorems/7d8fa1a0-6396-471d-8d14-f1ff72deda33
-- title:
--   Ux3: rn of
-- statement:
--   The Ux3 construction uses the rn of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L630-L634
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L630-L634

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux3
variable {k j ρ : ℕ}

theorem Formalism.FourierDecayAlt.P.Ux3.rn_of (c : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (S : Matrix (Fin j) (Fin j) ℂ) (hS : Sᴴ = -S) :
    Rn k j ρ (Matrix.of.symm c, skewCoords S) = blk3 1 (-(G.wMat j * cᴴ * Hpk k ρ))
      (G.wMat j * ((-(1 / 2 : ℂ)) • (cᴴ * Hpk k ρ * c) + S)) 0 1 c 0 0 1 := by sorry

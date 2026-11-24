-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_fm_eq
-- name    : Formalism.FourierDecayAlt.P.Ux3.fm_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:26:15.04627+00:00
-- url     : https://prove2.me/theorems/fc02a5ec-b4a4-40ab-9c48-67336990c952
-- title:
--   Ux3: fm eq
-- statement:
--   The Ux3 construction uses the fm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L296-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L296-L327

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

theorem Formalism.FourierDecayAlt.P.Ux3.fm_eq (z : Fin (2 * (j + ρ) + k + 1) → ℂ) (hz : inWb k (j + ρ) z) :
    Formalism.QuantumDeterminants.Fm k (j + ρ) z = Matrix.reindex (eB k j ρ) (eC j ρ) (F0 (Formalism.QuantumDeterminants.Fm k ρ (lowV k j ρ z))) := by sorry

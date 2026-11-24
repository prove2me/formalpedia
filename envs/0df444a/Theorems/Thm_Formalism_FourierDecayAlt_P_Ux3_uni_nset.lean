-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_uni_nset
-- name    : Formalism.FourierDecayAlt.P.Ux3.uni_nset
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:27:21.558394+00:00
-- url     : https://prove2.me/theorems/b55edab9-633a-4d16-b90e-8c4194cf8af3
-- title:
--   Ux3: uni nset
-- statement:
--   The Ux3 construction uses the uni nset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L241-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L241-L271

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

theorem Formalism.FourierDecayAlt.P.Ux3.uni_nset (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (hU : (blk3 1 A12 A13 0 1 A23 0 0 1)ᴴ * Hpk k (j + ρ) * blk3 1 A12 A13 0 1 A23 0 0 1 = Hpk k (j + ρ)) :
    blk3 1 A12 A13 0 1 A23 0 0 1 ∈ Nset k (j + ρ) := by sorry

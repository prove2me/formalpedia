-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_rn_eq
-- name    : Formalism.FourierDecayAlt.P.Ux3.rn_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:47:51.617292+00:00
-- url     : https://prove2.me/theorems/7071863a-e968-418b-806d-0b640a2a816b
-- title:
--   Ux3: rn eq
-- statement:
--   The Ux3 construction uses the rn eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L95-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L95-L97

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

theorem Formalism.FourierDecayAlt.P.Ux3.rn_eq (x : RC k j ρ) : Rn k j ρ x = blk3 1 (-(G.wMat j * (Matrix.of x.1)ᴴ * Hpk k ρ))
    (G.wMat j * ((-(1 / 2 : ℂ)) • ((Matrix.of x.1)ᴴ * Hpk k ρ * Matrix.of x.1) + skewOf x.2))
    0 1 (Matrix.of x.1) 0 0 1 := by sorry

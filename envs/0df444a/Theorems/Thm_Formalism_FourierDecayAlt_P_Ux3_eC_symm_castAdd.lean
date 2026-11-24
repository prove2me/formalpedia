-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_eC_symm_castAdd
-- name    : Formalism.FourierDecayAlt.P.Ux3.eC_symm_castAdd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:25:49.222093+00:00
-- url     : https://prove2.me/theorems/e9e726c4-911e-4f51-9d7b-12f9caf77e4a
-- title:
--   Ux3: e C symm cast Add
-- statement:
--   The Ux3 construction uses the e C symm cast Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L358-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L358-L362

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

theorem Formalism.FourierDecayAlt.P.Ux3.eC_symm_castAdd {l : ℕ} (h : j + l ≤ j + ρ + 1) (a : Fin j) :
    (eC j ρ).symm (Fin.castLE h (Fin.castAdd l a)) = Sum.inl a := by sorry

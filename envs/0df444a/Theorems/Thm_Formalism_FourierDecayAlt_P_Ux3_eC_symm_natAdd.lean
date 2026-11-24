-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_eC_symm_natAdd
-- name    : Formalism.FourierDecayAlt.P.Ux3.eC_symm_natAdd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:25:51.34244+00:00
-- url     : https://prove2.me/theorems/eeea1cd5-a507-48f7-97de-72d97d051fe9
-- title:
--   Ux3: e C symm nat Add
-- statement:
--   The Ux3 construction uses the e C symm nat Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L364-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L364-L368

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

theorem Formalism.FourierDecayAlt.P.Ux3.eC_symm_natAdd {l : ℕ} (h : j + l ≤ j + ρ + 1) (hl : l ≤ ρ + 1) (c : Fin l) :
    (eC j ρ).symm (Fin.castLE h (Fin.natAdd j c)) = Sum.inr (Fin.castLE hl c) := by sorry

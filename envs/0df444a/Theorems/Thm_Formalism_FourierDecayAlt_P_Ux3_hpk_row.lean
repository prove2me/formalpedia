-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_hpk_row
-- name    : Formalism.FourierDecayAlt.P.Ux3.hpk_row
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:26:14.50386+00:00
-- url     : https://prove2.me/theorems/7617387f-671c-4731-a4ff-287aede0b8e8
-- title:
--   Ux3: hpk row
-- statement:
--   The Ux3 construction uses the hpk row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L106-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L106-L124

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_row

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

theorem Formalism.FourierDecayAlt.P.Ux3.hpk_row (k r : ℕ) (a : ℕ) (ha : a < r) (c : Fin (2 * r + k + 1)) :
    Hpk k r ⟨a, by omega⟩ c = if c = ⟨2 * r + k - a, by omega⟩ then 1 else 0 := by sorry

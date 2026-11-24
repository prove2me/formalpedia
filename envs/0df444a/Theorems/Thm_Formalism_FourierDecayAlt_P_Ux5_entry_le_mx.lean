-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_entry_le_mx
-- name    : Formalism.FourierDecayAlt.P.Ux5.entry_le_mx
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:29:58.452393+00:00
-- url     : https://prove2.me/theorems/b97ebeb7-b6ce-40a0-9658-0ced32464c9e
-- title:
--   Ux5: entry le mx
-- statement:
--   The Ux5 construction uses the entry le mx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L70-L73

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5

theorem Formalism.FourierDecayAlt.P.Ux5.entry_le_mx {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) (i : m) (j : n) :
    ‖A i j‖ ≤ mx A := by sorry

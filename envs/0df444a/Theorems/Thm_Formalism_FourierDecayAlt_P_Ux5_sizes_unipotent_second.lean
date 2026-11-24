-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_sizes_unipotent_second
-- name    : Formalism.FourierDecayAlt.P.Ux5.sizes_unipotent_second
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:29:05.904024+00:00
-- url     : https://prove2.me/theorems/e788df7c-fcef-4a71-8688-fe6216e75e33
-- title:
--   Ux5: sizes unipotent second
-- statement:
--   The Ux5 construction uses the sizes unipotent second property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L203-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L203-L206

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

theorem Formalism.FourierDecayAlt.P.Ux5.sizes_unipotent_second {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ) (C : Matrix (Fin s) (Fin p) ℂ)
    (D : Matrix (Fin s) (Fin s) ℂ) (i : Fin s) (j : Fin p) :
    blk2 A B C D (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = C i j := by sorry

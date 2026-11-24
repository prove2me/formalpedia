-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_beta_id
-- name    : Formalism.FourierDecayAlt.P.Ux5.beta_id
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:29:43.042982+00:00
-- url     : https://prove2.me/theorems/06b38cf0-a8cb-4990-af06-0850e897fdda
-- title:
--   Ux5: beta id
-- statement:
--   The Ux5 construction uses the beta id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L680-L698
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Block3MulBlocks.lean#L680-L698

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

theorem Formalism.FourierDecayAlt.P.Ux5.beta_id {N j : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (c : Matrix (Fin N) (Fin j) ℂ)
    (S : Matrix (Fin j) (Fin j) ℂ) (hH : Hᴴ = H) (hS : Sᴴ = -S) :
    G.wMat j * ((-(1 / 2 : ℂ)) • (cᴴ * H * c) + S) =
      -(G.wMat j * (G.wMat j * ((-(1 / 2 : ℂ)) • (cᴴ * H * c) + S) - (-(G.wMat j * cᴴ * H)) * c)ᴴ *
        G.wMat j) := by sorry

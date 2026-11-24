-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_xC_ne_of_im
-- name    : Formalism.FourierDecayAlt.P.NFx2.xC_ne_of_im
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:17:53.553803+00:00
-- url     : https://prove2.me/theorems/e3bc5a33-f193-4eb4-83f2-296a764a6ee4
-- title:
--   NFx2: x C ne of im
-- statement:
--   The NFx2 construction uses the x C ne of im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L389-L395
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean#L389-L395

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section

theorem Formalism.FourierDecayAlt.P.NFx2.xC_ne_of_im (P : M.Par) (ρ : M.Ty P) {Y : ℂ} (h : Y.im ≠ 0) : M.xC P ρ Y ≠ 0 := by sorry

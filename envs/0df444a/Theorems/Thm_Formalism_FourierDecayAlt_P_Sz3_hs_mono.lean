-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_hs_mono
-- name    : Formalism.FourierDecayAlt.P.Sz3.hs_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:07.172383+00:00
-- url     : https://prove2.me/theorems/ba281e58-fe32-4d8e-bf0e-f1566c76e1c8
-- title:
--   Sz3: hs mono
-- statement:
--   The Sz3 construction uses the hs mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L266-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L266-L269

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz3
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz3.hs_mono (p J : ℕ) (h : p ≤ J) : hs p ≤ hs J := by sorry

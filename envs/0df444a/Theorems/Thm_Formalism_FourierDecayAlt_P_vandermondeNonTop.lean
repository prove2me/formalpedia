-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_vandermondeNonTop
-- name    : Formalism.FourierDecayAlt.P.vandermondeNonTop
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:05.661166+00:00
-- url     : https://prove2.me/theorems/7e46a6a6-6636-4550-a9be-b80ca1b0b213
-- title:
--   P: vandermonde Non Top
-- statement:
--   The P construction uses the vandermonde Non Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L376-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L376-L384

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.Sz Formalism.FourierDecayAlt.P.Sz4

theorem Formalism.FourierDecayAlt.P.vandermondeNonTop : Formalism.FourierDecayAlt.Sz.VandNonTop := by sorry

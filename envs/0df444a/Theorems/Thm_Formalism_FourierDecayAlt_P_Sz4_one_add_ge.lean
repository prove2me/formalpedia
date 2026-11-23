-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_one_add_ge
-- name    : Formalism.FourierDecayAlt.P.Sz4.one_add_ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:07.669366+00:00
-- url     : https://prove2.me/theorems/293afe66-cc62-4b59-819c-240f5ca3ab70
-- title:
--   Sz4: one add ge
-- statement:
--   The Sz4 construction uses the one add ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L93-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L93-L115

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz4.one_add_ge (t : ℝ) (ht : |t| ≤ 1 / 4) : Real.exp (t - 2 / 3 * t ^ 2) ≤ 1 + t := by sorry

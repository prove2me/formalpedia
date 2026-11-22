-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_u_last
-- name    : Formalism.FourierDecayAlt.P.Sz4.u_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:56:52.92447+00:00
-- url     : https://prove2.me/theorems/db063033-7093-45fd-b3c7-2a2fc4ef9bea
-- title:
--   Sz4: u last
-- statement:
--   The Sz4 construction uses the u last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L596-L598
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L596-L598

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

theorem Formalism.FourierDecayAlt.P.Sz4.u_last (c : Cfg) (de : ℕ → ℝ) (hc : c.Ok) : c.u de c.k = c.ulast := by sorry

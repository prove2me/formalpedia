-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_harm_log
-- name    : Formalism.FourierDecayAlt.P.Sz4.harm_log
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:05.635751+00:00
-- url     : https://prove2.me/theorems/29c97628-ee97-4416-adea-7e80b75e17bd
-- title:
--   Sz4: harm log
-- statement:
--   The Sz4 construction uses the harm log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L57-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L57-L68

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

theorem Formalism.FourierDecayAlt.P.Sz4.harm_log (h n : ℕ) (hh : 1 ≤ h) (hn : h ≤ n) :
    ∑ d ∈ Ioc h n, (1 : ℝ) / d ≤ Real.log n - Real.log h := by sorry

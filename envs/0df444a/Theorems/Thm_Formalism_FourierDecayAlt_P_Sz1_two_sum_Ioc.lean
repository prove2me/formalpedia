-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz1_two_sum_Ioc
-- name    : Formalism.FourierDecayAlt.P.Sz1.two_sum_Ioc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:35.303821+00:00
-- url     : https://prove2.me/theorems/e0e42dea-4ff1-4677-9e6c-580b33d1375d
-- title:
--   Sz1: two sum Ioc
-- statement:
--   The Sz1 construction uses the two sum Ioc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MassRatioFormula.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MassRatioFormula.lean#L13-L17

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz1
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz1.two_sum_Ioc (k p : ℕ) : 2 * ∑ M ∈ Ioc k (k + p), M = 2 * (p * k) + p * (p + 1) := by sorry

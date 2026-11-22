-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G5_symm_castSucc
-- name    : Formalism.FourierDecayAlt.P.G5.symm_castSucc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:54:41.188461+00:00
-- url     : https://prove2.me/theorems/58037856-bfc0-4c2b-8849-27a2989c0614
-- title:
--   G5: symm cast Succ
-- statement:
--   The G5 construction uses the symm cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L127-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L127-L129

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.G5.symm_castSucc {n : ℕ} (i : Fin n) :
    finSumFinEquiv.symm (i.castSucc : Fin (n + 1)) = Sum.inl i := by sorry

-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G2_symm_castSucc
-- name    : Formalism.FourierDecayAlt.P.G2.symm_castSucc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:53:35.176675+00:00
-- url     : https://prove2.me/theorems/6b143130-787d-4ca1-8444-de519f41ca25
-- title:
--   G2: symm cast Succ
-- statement:
--   The G2 construction uses the symm cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdditiveCharacterPsi.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdditiveCharacterPsi.lean#L12-L14

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
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
set_option linter.unnecessarySeqFocus false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G2
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.G2.symm_castSucc {n : ℕ} (i : Fin n) :
    finSumFinEquiv.symm (i.castSucc : Fin (n + 1)) = Sum.inl i := by sorry

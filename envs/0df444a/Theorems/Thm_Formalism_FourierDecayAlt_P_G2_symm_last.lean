-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G2_symm_last
-- name    : Formalism.FourierDecayAlt.P.G2.symm_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:53:20.685068+00:00
-- url     : https://prove2.me/theorems/d81ccfa7-5558-4d6c-9421-3b5161c1e058
-- title:
--   G2: symm last
-- statement:
--   The G2 construction uses the symm last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdditiveCharacterPsi.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdditiveCharacterPsi.lean#L16-L17

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

theorem Formalism.FourierDecayAlt.P.G2.symm_last (n : ℕ) : finSumFinEquiv.symm (Fin.last n : Fin (n + 1)) = Sum.inr (0 : Fin 1) := by sorry

-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz1_colIdx_ne_zero
-- name    : Formalism.FourierDecayAlt.P.Sz1.colIdx_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:34.259815+00:00
-- url     : https://prove2.me/theorems/9f8f2479-d367-48a5-94a5-6dc2226e2e3f
-- title:
--   Sz1: col Idx ne zero
-- statement:
--   The Sz1 construction uses the col Idx ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MassRatioFormula.lean#L62-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MassRatioFormula.lean#L62-L65

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

theorem Formalism.FourierDecayAlt.P.Sz1.colIdx_ne_zero (k : ℕ) (q : ℝ) (hq : 1 < q) : colIdx k q ≠ 0 := by sorry

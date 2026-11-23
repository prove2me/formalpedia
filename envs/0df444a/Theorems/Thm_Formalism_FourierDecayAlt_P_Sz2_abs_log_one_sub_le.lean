-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_abs_log_one_sub_le
-- name    : Formalism.FourierDecayAlt.P.Sz2.abs_log_one_sub_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:48.435986+00:00
-- url     : https://prove2.me/theorems/c0faeeae-8bc0-4212-a1d6-9db4a05c9696
-- title:
--   Sz2: abs log one sub le
-- statement:
--   The Sz2 construction uses the abs log one sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CorollaryAOfPropositionA.lean#L68-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CorollaryAOfPropositionA.lean#L68-L78

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz2
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz2.abs_log_one_sub_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) :
    |Real.log (1 - x)| ≤ 2 * x := by sorry

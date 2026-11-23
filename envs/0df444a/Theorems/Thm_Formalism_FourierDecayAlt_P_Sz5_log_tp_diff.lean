-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_log_tp_diff
-- name    : Formalism.FourierDecayAlt.P.Sz5.log_tp_diff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:32.612904+00:00
-- url     : https://prove2.me/theorems/c4920009-bfab-4fb8-89b9-9950cbb7b623
-- title:
--   Sz5: log tp diff
-- statement:
--   The Sz5 construction uses the log tp diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L816-L825
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L816-L825

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz5
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz5.log_tp_diff (k m : ℕ) (ka rd g VV V V' : ℝ) (hka : 0 < ka) (hrd : 0 < rd) (hg : 0 < g)
    (hVV : 0 < VV) (hV : 0 < V) (hV' : 0 < V') :
    Real.log (TcritPow k m ka rd g VV V) - Real.log (TcritPow k m ka rd g VV V') =
      Real.log (V' / V) := by sorry

-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_u_mid_bounds
-- name    : Formalism.FourierDecayAlt.P.Sz5.u_mid_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:48.739392+00:00
-- url     : https://prove2.me/theorems/fb14c134-efbd-41b6-bf2f-d713c3916a1f
-- title:
--   Sz5: u mid bounds
-- statement:
--   The Sz5 construction uses the u mid bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L482-L490
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L482-L490

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

theorem Formalism.FourierDecayAlt.P.Sz5.u_mid_bounds (c : Cfg) (h : c.Ok) (de : ℕ → ℝ) (hw : IsWord c.k de) (j : ℕ) (h1 : 1 ≤ j)
    (h2 : j + 2 ≤ c.k) : 0 ≤ c.u de (j + 1) ∧ c.u de (j + 1) ≤ c.v 1 := by sorry

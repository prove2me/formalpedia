-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_u_mid
-- name    : Formalism.FourierDecayAlt.P.Sz5.u_mid
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:37:01.807809+00:00
-- url     : https://prove2.me/theorems/c42fdbf3-055a-4102-bd1c-29d3715cdfba
-- title:
--   Sz5: u mid
-- statement:
--   The Sz5 construction uses the u mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L471-L476
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L471-L476

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_u_mid

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

theorem Formalism.FourierDecayAlt.P.Sz5.u_mid (c : Cfg) (de : ℕ → ℝ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j + 2 ≤ c.k) :
    c.u de (j + 1) = c.v j - 1 / 2 - de j * c.Del := by sorry

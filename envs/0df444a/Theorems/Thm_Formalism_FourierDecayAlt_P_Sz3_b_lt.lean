-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_b_lt
-- name    : Formalism.FourierDecayAlt.P.Sz3.b_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:05.056746+00:00
-- url     : https://prove2.me/theorems/b3db651e-a3e3-47e4-a7c3-fa19dd1ebd27
-- title:
--   Sz3: b lt
-- statement:
--   The Sz3 construction uses the b lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L7-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L7-L19

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz3
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz3.b_lt (c : Cfg) (hc : c.Ok) (j : ℕ) (hj : 1 ≤ j) :
    ∀ j' : ℕ, j < j' → j' ≤ c.m → c.b j < c.b j' := by sorry

-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_lin_bound
-- name    : Formalism.FourierDecayAlt.P.Sz4.lin_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:25:53.295456+00:00
-- url     : https://prove2.me/theorems/9c613e97-971b-44a2-b4bf-b0316894f45d
-- title:
--   Sz4: lin bound
-- statement:
--   The Sz4 construction uses the lin bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L117-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L117-L170

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz4.lin_bound (J : ℕ) (hJ : 1 ≤ J) (de : ℕ → ℝ) (h01 : ∀ i, de i = 0 ∨ de i = 1) :
    |∑ i ∈ Icc 1 J, ∑ j ∈ Ioc i J, (de j - de i) / (4 * ((j : ℝ) - (i : ℝ)))| ≤
      (1 + J * Real.log 2) / 4 := by sorry

-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_shift_bound1
-- name    : Formalism.FourierDecayAlt.P.Sz4.shift_bound1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:07.444393+00:00
-- url     : https://prove2.me/theorems/d9079e53-84fe-45d8-bf82-71af10aa91cb
-- title:
--   Sz4: shift bound1
-- statement:
--   The Sz4 construction uses the shift bound1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L30-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L30-L47

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

theorem Formalism.FourierDecayAlt.P.Sz4.shift_bound1 (de : ℕ → ℝ) (h01 : ∀ i, de i = 0 ∨ de i = 1) (n d : ℕ) :
    |∑ i ∈ Icc 1 n, (de (i + d) - de i)| ≤ d := by sorry

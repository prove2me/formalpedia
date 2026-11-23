-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_prod_shift_Ioc
-- name    : Formalism.FourierDecayAlt.P.Sz4.prod_shift_Ioc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:16.818076+00:00
-- url     : https://prove2.me/theorems/e36744bd-1905-4375-b3c0-1d5317385d9b
-- title:
--   Sz4: prod shift Ioc
-- statement:
--   The Sz4 construction uses the prod shift Ioc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L260-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L260-L267

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

theorem Formalism.FourierDecayAlt.P.Sz4.prod_shift_Ioc (i p : ℕ) (f : ℕ → ℝ) :
    ∏ j ∈ Ioc i p, f (j + 1) = ∏ j ∈ Ioc (i + 1) (p + 1), f j := by sorry

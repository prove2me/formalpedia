-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_prod_refl
-- name    : Formalism.FourierDecayAlt.P.Sz4.prod_refl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:07.707841+00:00
-- url     : https://prove2.me/theorems/24a73e82-c8fe-411a-b28a-5ff0c4c1b344
-- title:
--   Sz4: prod refl
-- statement:
--   The Sz4 construction uses the prod refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L307-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L307-L319

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

theorem Formalism.FourierDecayAlt.P.Sz4.prod_refl (p : ℕ) : ∏ i ∈ Icc 1 p, (((p + 1 : ℕ) : ℝ) - (i : ℝ)) = (p.factorial : ℝ) := by sorry

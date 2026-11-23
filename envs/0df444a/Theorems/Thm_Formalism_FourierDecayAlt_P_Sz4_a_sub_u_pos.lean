-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_a_sub_u_pos
-- name    : Formalism.FourierDecayAlt.P.Sz4.a_sub_u_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:14:23.791536+00:00
-- url     : https://prove2.me/theorems/9d4debe5-3367-4227-841b-b130824b2e19
-- title:
--   Sz4: a sub u pos
-- statement:
--   The Sz4 construction uses the a sub u pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L473-L477
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L473-L477

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

theorem Formalism.FourierDecayAlt.P.Sz4.a_sub_u_pos (c : Cfg) (de : ℕ → ℝ) (hc : c.Ok) (hw : IsWord c.k de) (i : ℕ)
    (hi : i ∈ Icc 2 (c.k - 1)) : 4 * c.k * c.Del ≤ c.a - c.u de i := by sorry

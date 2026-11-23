-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_u_mid_diff
-- name    : Formalism.FourierDecayAlt.P.Sz4.u_mid_diff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:21.025975+00:00
-- url     : https://prove2.me/theorems/f1561f03-a73f-4cd1-9327-3d3052156a8d
-- title:
--   Sz4: u mid diff
-- statement:
--   The Sz4 construction uses the u mid diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L464-L471
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L464-L471

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

theorem Formalism.FourierDecayAlt.P.Sz4.u_mid_diff (c : Cfg) (de de' : ℕ → ℝ) (hc : c.Ok) (hw : IsWord c.k de)
    (hw' : IsWord c.k de') (i : ℕ) (hi : i ∈ Icc 2 (c.k - 1)) :
    |c.u de i - c.u de' i| ≤ c.Del := by sorry

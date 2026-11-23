-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_top_ratio_le
-- name    : Formalism.FourierDecayAlt.P.Sz4.top_ratio_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:04.05535+00:00
-- url     : https://prove2.me/theorems/15967fbe-bbc6-4102-9dc9-97422c1add9a
-- title:
--   Sz4: top ratio le
-- statement:
--   The Sz4 construction uses the top ratio le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L525-L545
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L525-L545

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

theorem Formalism.FourierDecayAlt.P.Sz4.top_ratio_le (c : Cfg) (de de' : ℕ → ℝ) (hc : c.Ok) (ht : c.top = true)
    (hw : IsWord c.k de) (hw' : IsWord c.k de') :
    ∏ i ∈ Icc 2 (c.k - 1), ((c.u de i + c.bp) / (c.u de' i + c.bp)) ≤ Real.exp (c.vthp / 3) := by sorry

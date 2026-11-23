-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_vand_le
-- name    : Formalism.FourierDecayAlt.P.Sz4.vand_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:25.981807+00:00
-- url     : https://prove2.me/theorems/9ea6b7d0-d1a9-4a1b-9b8e-16a61ae7f108
-- title:
--   Sz4: vand le
-- statement:
--   The Sz4 construction uses the vand le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L671-L730
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L671-L730

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

theorem Formalism.FourierDecayAlt.P.Sz4.vand_le (c : Cfg) (de de' : ℕ → ℝ) (hc : c.Ok) (hv : c.vth ≤ 1 / 10) (hw : IsWord c.k de)
    (hw' : IsWord c.k de') :
    0 < Vand c.k (c.u de) ∧
      Vand c.k (c.u de') ≤ Real.exp ((c.k : ℝ) / 2 + 1) * Vand c.k (c.u de) := by sorry

-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_vand_u_decomp
-- name    : Formalism.FourierDecayAlt.P.Sz4.vand_u_decomp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:26.003431+00:00
-- url     : https://prove2.me/theorems/23c15ecb-b253-4855-9b09-4a16d06716c6
-- title:
--   Sz4: vand u decomp
-- statement:
--   The Sz4 construction uses the vand u decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L614-L624
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L614-L624

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

theorem Formalism.FourierDecayAlt.P.Sz4.vand_u_decomp (c : Cfg) (de : ℕ → ℝ) (hc : c.Ok) :
    Vand c.k (c.u de) = (∏ j ∈ Icc 2 (c.k - 1), (c.a - c.u de j)) * (c.a - c.ulast) *
      Vand (c.k - 1) (fun i => c.u de (i + 1)) := by sorry

-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_vand_top_decomp
-- name    : Formalism.FourierDecayAlt.P.Sz4.vand_top_decomp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:25.661022+00:00
-- url     : https://prove2.me/theorems/40454d86-d4dd-4037-a3df-c0fa4c005a27
-- title:
--   Sz4: vand top decomp
-- statement:
--   The Sz4 construction uses the vand top decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L626-L638
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L626-L638

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

theorem Formalism.FourierDecayAlt.P.Sz4.vand_top_decomp (c : Cfg) (de : ℕ → ℝ) (hc : c.Ok) (ht : c.top = true) :
    Vand (c.k - 1) (fun i => c.u de (i + 1)) =
      Vand (c.k - 2) (fun i => c.u de (i + 1)) * ∏ i ∈ Icc 2 (c.k - 1), (c.u de i + c.bp) := by sorry

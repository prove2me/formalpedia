-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_edge_factor
-- name    : Formalism.FourierDecayAlt.P.Sz4.edge_factor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:56.714334+00:00
-- url     : https://prove2.me/theorems/f4f96121-9850-4a9b-b3e8-37e74f5a6a6e
-- title:
--   Sz4: edge factor
-- statement:
--   The Sz4 construction uses the edge factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L420-L437
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L420-L437

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

theorem Formalism.FourierDecayAlt.P.Sz4.edge_factor (c : Cfg) (de : ℕ → ℝ) (hc : c.Ok) (hw : IsWord c.k de) (i : ℕ) (h2 : 2 ≤ i)
    (hik : i ≤ c.k) (h : i < c.k ∨ c.top = false) :
    c.a - c.v 1 ≤ c.a - c.u de i ∧ c.a - c.u de i ≤ 2 * (c.a - c.v 1) := by sorry

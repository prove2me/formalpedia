-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_u_mid_nonneg
-- name    : Formalism.FourierDecayAlt.P.Sz4.u_mid_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:14:29.859302+00:00
-- url     : https://prove2.me/theorems/7680031e-a54e-4139-a52b-a2ac71a5888f
-- title:
--   Sz4: u mid nonneg
-- statement:
--   The Sz4 construction uses the u mid nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L514-L523
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L514-L523

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

theorem Formalism.FourierDecayAlt.P.Sz4.u_mid_nonneg (c : Cfg) (de : ℕ → ℝ) (hc : c.Ok) (hw : IsWord c.k de) (i : ℕ)
    (hi : i ∈ Icc 2 (c.k - 1)) : 0 ≤ c.u de i := by sorry

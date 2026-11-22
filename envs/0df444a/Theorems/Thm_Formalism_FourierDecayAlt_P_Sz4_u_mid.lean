-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_u_mid
-- name    : Formalism.FourierDecayAlt.P.Sz4.u_mid
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:58:07.437814+00:00
-- url     : https://prove2.me/theorems/49cfd8db-ce8b-452a-9567-ddc4d8707a26
-- title:
--   Sz4: u mid
-- statement:
--   The Sz4 construction uses the u mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L458-L462
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L458-L462

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

theorem Formalism.FourierDecayAlt.P.Sz4.u_mid (c : Cfg) (de : ℕ → ℝ) (hw : IsWord c.k de) (i : ℕ) (hi : i ∈ Icc 2 (c.k - 1)) :
    c.u de i = c.v (i - 1) - 1 / 2 - de (i - 1) * c.Del := by sorry

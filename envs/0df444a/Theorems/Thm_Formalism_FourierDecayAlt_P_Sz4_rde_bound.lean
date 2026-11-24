-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_rde_bound
-- name    : Formalism.FourierDecayAlt.P.Sz4.rde_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:21.348515+00:00
-- url     : https://prove2.me/theorems/d40cfd03-2cc6-47d8-880f-3e100c1a4a17
-- title:
--   Sz4: rde bound
-- statement:
--   The Sz4 construction uses the rde bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L209-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L209-L250

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

theorem Formalism.FourierDecayAlt.P.Sz4.rde_bound (J : ℕ) (hJ : 1 ≤ J) (de : ℕ → ℝ) (h01 : ∀ i, de i = 0 ∨ de i = 1) :
    Real.exp (-(((J : ℝ) + 1) / 4)) ≤ Rde J de ∧ Rde J de ≤ Real.exp (((J : ℝ) + 1) / 4) := by sorry

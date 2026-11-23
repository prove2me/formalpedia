-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_position_ratio
-- name    : Formalism.FourierDecayAlt.P.Sz4.position_ratio
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:13.716724+00:00
-- url     : https://prove2.me/theorems/43fc794b-6f66-426c-afc1-5c639c09505e
-- title:
--   Sz4: position ratio
-- statement:
--   The Sz4 construction uses the position ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L346-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L346-L356

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

theorem Formalism.FourierDecayAlt.P.Sz4.position_ratio (c : Cfg) (de : ℕ → ℝ) (hw : IsWord c.k de) (i j : ℕ) (hi : 1 ≤ i)
    (hij : i < j) (hj : j + 1 ≤ c.k) (h : j + 2 ≤ c.k ∨ c.top = false) :
    c.u de (i + 1) - c.u de (j + 1) =
      (1 + (de j - de i) / (4 * ((j : ℝ) - (i : ℝ)))) * (c.v i - c.v j) := by sorry

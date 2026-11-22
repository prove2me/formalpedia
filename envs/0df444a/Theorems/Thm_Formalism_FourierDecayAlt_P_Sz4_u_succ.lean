-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_u_succ
-- name    : Formalism.FourierDecayAlt.P.Sz4.u_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:14:23.209809+00:00
-- url     : https://prove2.me/theorems/c68d7a17-a022-42a1-933a-8f575c5973a1
-- title:
--   Sz4: u succ
-- statement:
--   The Sz4 construction uses the u succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L330-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L330-L344

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

theorem Formalism.FourierDecayAlt.P.Sz4.u_succ (c : Cfg) (de : ℕ → ℝ) (hw : IsWord c.k de) (i : ℕ) (hi : 1 ≤ i)
    (_hik : i + 1 ≤ c.k) (h : i + 2 ≤ c.k ∨ c.top = false) :
    c.u de (i + 1) = c.v i - 1 / 2 - de i * c.Del := by sorry

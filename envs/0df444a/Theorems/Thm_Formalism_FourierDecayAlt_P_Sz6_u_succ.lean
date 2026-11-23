-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz6_u_succ
-- name    : Formalism.FourierDecayAlt.P.Sz6.u_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:58.142807+00:00
-- url     : https://prove2.me/theorems/c19c7da1-0970-45e9-a34f-c2ff8181f6ed
-- title:
--   Sz6: u succ
-- statement:
--   The Sz6 construction uses the u succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaFactorisation.lean#L51-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaFactorisation.lean#L51-L64

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaFactorisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.Sz Finset
open Formalism.FourierDecayAlt.P.Sz6

theorem Formalism.FourierDecayAlt.P.Sz6.u_succ (c : Cfg) (de : ℕ → ℝ) (hw : IsWord c.k de) (i : ℕ) (hi : 1 ≤ i)
    (hnt : ¬ (c.top = true ∧ i + 1 = c.k)) :
    c.u de (i + 1) = c.v i - 1 / 2 - de i * c.Del := by sorry

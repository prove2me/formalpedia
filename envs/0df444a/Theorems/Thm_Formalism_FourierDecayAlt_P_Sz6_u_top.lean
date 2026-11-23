-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz6_u_top
-- name    : Formalism.FourierDecayAlt.P.Sz6.u_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:55.80983+00:00
-- url     : https://prove2.me/theorems/120b3f80-5d3e-40c5-ba3a-43ee617af7f3
-- title:
--   Sz6: u top
-- statement:
--   The Sz6 construction uses the u top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaFactorisation.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaFactorisation.lean#L66-L69

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

theorem Formalism.FourierDecayAlt.P.Sz6.u_top (c : Cfg) (de : ℕ → ℝ) (i : ℕ) (hi : 1 ≤ i) (ht : c.top = true)
    (hk : i + 1 = c.k) : c.u de (i + 1) = -c.bp := by sorry

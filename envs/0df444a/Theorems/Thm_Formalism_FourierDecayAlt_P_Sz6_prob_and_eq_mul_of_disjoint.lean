-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz6_prob_and_eq_mul_of_disjoint
-- name    : Formalism.FourierDecayAlt.P.Sz6.prob_and_eq_mul_of_disjoint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:51.075925+00:00
-- url     : https://prove2.me/theorems/236d484e-2f56-4661-a358-e0c772d406e6
-- title:
--   Sz6: prob and eq mul of disjoint
-- statement:
--   The Sz6 construction uses the prob and eq mul of disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaFactorisation.lean#L21-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaFactorisation.lean#L21-L43

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

theorem Formalism.FourierDecayAlt.P.Sz6.prob_and_eq_mul_of_disjoint (c : Cfg) (hk : 1 ≤ c.k) (Y : ℝ) :
    c.P Y = (∏ i ∈ Icc 1 (c.k - 1), (Y + c.v i)) * ∏ j ∈ Icc 1 c.m, (Y - c.b j) := by sorry

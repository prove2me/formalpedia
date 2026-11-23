-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz6_prod_split_first
-- name    : Formalism.FourierDecayAlt.P.Sz6.prod_split_first
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:58.799109+00:00
-- url     : https://prove2.me/theorems/c11e98f6-96db-4ecd-90e5-9e86210beff2
-- title:
--   Sz6: prod split first
-- statement:
--   The Sz6 construction uses the prod split first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaFactorisation.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaFactorisation.lean#L45-L49

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

theorem Formalism.FourierDecayAlt.P.Sz6.prod_split_first (k : ℕ) (hk : 1 ≤ k) (F : ℕ → ℝ) :
    ∏ i ∈ Icc 1 k, F i = F 1 * ∏ i ∈ Icc 1 (k - 1), F (i + 1) := by sorry

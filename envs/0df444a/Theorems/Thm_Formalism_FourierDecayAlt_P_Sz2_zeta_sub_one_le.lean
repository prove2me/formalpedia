-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz2_zeta_sub_one_le
-- name    : Formalism.FourierDecayAlt.P.Sz2.zeta_sub_one_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:35.843987+00:00
-- url     : https://prove2.me/theorems/ab2c86db-e85b-45e5-b7bc-1e91e42e5bf1
-- title:
--   Sz2: zeta sub one le
-- statement:
--   The Sz2 construction uses the zeta sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CorollaryAOfPropositionA.lean#L47-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CorollaryAOfPropositionA.lean#L47-L57

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz2
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz2.zeta_sub_one_le (M : ℕ) (hM : 3 ≤ M) :
    ∑' j : ℕ, 1 / ((j : ℝ) + 1) ^ M ≤ 1 + 2 / 2 ^ M := by sorry

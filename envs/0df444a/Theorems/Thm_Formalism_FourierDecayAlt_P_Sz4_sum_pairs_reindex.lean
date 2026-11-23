-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_sum_pairs_reindex
-- name    : Formalism.FourierDecayAlt.P.Sz4.sum_pairs_reindex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:08.211973+00:00
-- url     : https://prove2.me/theorems/340f20f0-7872-41df-8e93-18058c326754
-- title:
--   Sz4: sum pairs reindex
-- statement:
--   The Sz4 construction uses the sum pairs reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L7-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L7-L23

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

theorem Formalism.FourierDecayAlt.P.Sz4.sum_pairs_reindex (J : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ i ∈ Icc 1 J, ∑ j ∈ Ioc i J, F i j =
      ∑ d ∈ Ioc 0 J, ∑ i ∈ Icc 1 (J - d), F i (i + d) := by sorry

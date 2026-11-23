-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_T0_SumDat_Ok_levels
-- name    : Formalism.MainNotions.Gaps.T0.SumDat.Ok.levels
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:22.722884+00:00
-- url     : https://prove2.me/theorems/92e08fa0-ca37-47db-a04c-79c5c0d08ade
-- title:
--   Ok: levels
-- statement:
--   The Ok construction uses the levels property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L283-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L283-L294

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FourTermSumBoundOfParameters
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_QuotientParamNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.T0
open Formalism.MainNotions.Gaps.T0.SumDat
variable {ι : Type*} (X : SumDat ι)
variable {X}

theorem Formalism.MainNotions.Gaps.T0.SumDat.Ok.levels (h : X.Ok) :
    X.R * (∑ la ∈ X.s, X.I la * X.l la + 1 / 2 * (X.T * (X.c / X.i) * ∑ la ∈ X.s, X.N la * X.l la)) ≤
      X.d * X.lev := by sorry

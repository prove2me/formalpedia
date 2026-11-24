-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_T0_SumDat_sum_split
-- name    : Formalism.MainNotions.Gaps.T0.SumDat.sum_split
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T09:56:07.551659+00:00
-- url     : https://prove2.me/theorems/4006eaea-3b10-4366-b2a4-717c145e6cde
-- title:
--   Sum Dat: sum split
-- statement:
--   The Sum Dat construction uses the sum split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L271-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L271-L281

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

theorem Formalism.MainNotions.Gaps.T0.SumDat.sum_split (X : SumDat ι) :
    ∑ la ∈ X.s, X.rr la * X.l la =
      X.R * (∑ la ∈ X.s, X.I la * X.l la + 1 / 2 * (X.T * (X.c / X.i) * ∑ la ∈ X.s, X.N la * X.l la))
        + ∑ la ∈ X.s, X.cD la * X.l la + ∑ la ∈ X.s, (X.vQ la + X.ρ' * X.be la) * X.l la := by sorry

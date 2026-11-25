-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_T0_SumDat_rr_nonneg
-- name    : Formalism.MainNotions.Gaps.T0.SumDat.rr_nonneg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:49:58.421869+00:00
-- url     : https://prove2.me/theorems/af85d8c2-ce96-5f6f-9e33-58c417630707
-- title:
--   Sum Dat: rr nonneg
-- statement:
--   The Sum Dat construction uses the rr nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L404-L409
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L404-L409

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

theorem Formalism.MainNotions.Gaps.T0.SumDat.rr_nonneg (X : SumDat ι) (la : ι) (h1 : 0 ≤ X.R * X.I la)
    (h2 : 0 ≤ X.R * (X.T * (X.c / (2 * X.i)) * X.N la)) (h3 : 0 ≤ X.cD la)
    (h4 : 0 ≤ X.vQ la + X.ρ' * X.be la) : 0 ≤ X.rr la := by sorry

-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_T0_SumDat_Ok_tsum_le_page
-- name    : Formalism.MainNotions.Gaps.T0.SumDat.Ok.tsum_le_page
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:50:15.125861+00:00
-- url     : https://prove2.me/theorems/a98d8f6d-9288-4d55-9a30-26be0bcffe2c
-- title:
--   Ok: tsum le page
-- statement:
--   The Ok construction uses the tsum le page property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L397-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/QuotientParamNonneg.lean#L397-L402

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

theorem Formalism.MainNotions.Gaps.T0.SumDat.Ok.tsum_le_page (h : X.Ok) {PP C k b m δ₂ q DF : ℝ} (hP : X.Rel PP)
    (hp : X.Page PP C k b m δ₂ q DF) (h0 : ∀ la ∉ X.s, X.rr la * X.l la = 0) :
    Summable (fun la => X.rr la * X.l la) ∧ ∑' la, X.rr la * X.l la ≤ X.d * X.f * m * b * δ₂ := by sorry

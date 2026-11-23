-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_kapL_le_kap
-- name    : Formalism.MainNotions.PlaneGram.kapL_le_kap
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:18.77039+00:00
-- url     : https://prove2.me/theorems/d0f95c42-f70d-4414-b77b-10c36b99017d
-- title:
--   Plane Gram: kap L le kap
-- statement:
--   The Plane Gram construction uses the kap L le kap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L404-L416
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L404-L416

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))

theorem Formalism.MainNotions.PlaneGram.kapL_le_kap {p : ℕ} (hp : 2 ≤ p) {r : ℕ} (hr : 1 ≤ r) {L : Type} [Fintype L] (d : L → ℕ) :
    kapL p r d + (Fintype.card L : ℝ) * r ≤ kap p r d := by sorry

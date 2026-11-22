-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_divE_apply
-- name    : Formalism.MainNotions.PlaneGram.divE_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:16:44.076334+00:00
-- url     : https://prove2.me/theorems/6d733d81-15a9-4835-a43a-26b4a99d50dc
-- title:
--   Plane Gram: div E apply
-- statement:
--   The Plane Gram construction uses the div E apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L126-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean#L126-L126

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
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
variable {K : Type} [Field K]
variable [CharZero K] (v : AddValuation K (WithTop ℚ)) (p : ℕ)

theorem Formalism.MainNotions.PlaneGram.divE_apply {r : ℕ} (P : ℕ) (η : Fin r →₀ ℕ) (a : Fin r) : divE P η a = η a / P := by sorry

attribute [defeq] Formalism.MainNotions.PlaneGram.divE_apply

-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_ddiv_eq
-- name    : Formalism.MainNotions.PlaneGram.ddiv_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:26:24.991947+00:00
-- url     : https://prove2.me/theorems/9b7a037e-c6ec-4e0d-99dc-3c2541112152
-- title:
--   Plane Gram: ddiv eq
-- statement:
--   The Plane Gram construction uses the ddiv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DigitPartMonomial.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DigitPartMonomial.lean#L35-L40

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
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

theorem Formalism.MainNotions.PlaneGram.ddiv_eq {σ : Type} (M : σ →₀ ℕ) (F : MvPolynomial σ K) : ddiv M F = ddivL M F := by sorry

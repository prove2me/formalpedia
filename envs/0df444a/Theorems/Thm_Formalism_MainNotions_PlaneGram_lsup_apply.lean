-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_lsup_apply
-- name    : Formalism.MainNotions.PlaneGram.lsup_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:15:31.673398+00:00
-- url     : https://prove2.me/theorems/8ac06ed1-1832-416c-84de-6eca1f22f4ed
-- title:
--   Plane Gram: lsup apply
-- statement:
--   The Plane Gram construction uses the lsup apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DigitPartMonomial.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DigitPartMonomial.lean#L19-L23

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

theorem Formalism.MainNotions.PlaneGram.lsup_apply {σ τ : Type} (φ : (σ →₀ ℕ) → MvPolynomial τ K) (F : MvPolynomial σ K) :
    lsup φ F = ∑ α ∈ F.support, F.coeff α • φ α := by sorry

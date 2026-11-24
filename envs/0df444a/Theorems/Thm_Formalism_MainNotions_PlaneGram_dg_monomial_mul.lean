-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_monomial_mul
-- name    : Formalism.MainNotions.PlaneGram.dg_monomial_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:06:31.604339+00:00
-- url     : https://prove2.me/theorems/7d7b964f-c515-4418-b97b-9fa7e7fbd00c
-- title:
--   Plane Gram: dg monomial mul
-- statement:
--   The Plane Gram construction uses the dg monomial mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1167-L1171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/AddMemSupportOfMemSupportCoefOut.lean#L1167-L1171

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
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

theorem Formalism.MainNotions.PlaneGram.dg_monomial_mul {σ : Type} (g : (σ →₀ ℕ) → K) (μ : σ →₀ ℕ) (Q : MvPolynomial σ K) :
    dg g (monomial μ 1 * Q) = monomial μ 1 * dg (fun β => g (μ + β)) Q := by sorry

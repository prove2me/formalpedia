-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_bge_dg
-- name    : Formalism.MainNotions.PlaneGram.bge_dg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:06:33.678751+00:00
-- url     : https://prove2.me/theorems/8b96b496-4ec1-46f1-b0a8-7f694ec9816c
-- title:
--   Plane Gram: bge dg
-- statement:
--   The Plane Gram construction uses the bge dg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L221-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/FockMonomialRight.lean#L221-L224

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapCastMono
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
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
variable (v : AddValuation K (WithTop ℚ)) {σ : Type}

theorem Formalism.MainNotions.PlaneGram.bge_dg {a b : ℝ} {f : (σ →₀ ℕ) → K} {F : MvPolynomial σ K} (hf : ∀ α, vge v a (f α))
    (hF : bge v b F) : bge v (a + b) (dg f F) := by sorry

-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_cge_dg
-- name    : Formalism.MainNotions.PlaneGram.cge_dg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:35.962689+00:00
-- url     : https://prove2.me/theorems/1c5cd7bf-caf6-4ded-9908-41e3411fe290
-- title:
--   Plane Gram: cge dg
-- statement:
--   The Plane Gram construction uses the cge dg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L151-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CgeZeroIffIntegral.lean#L151-L155

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

theorem Formalism.MainNotions.PlaneGram.cge_dg {σ : Type} {a b : ℝ} {f : (σ →₀ ℕ) → K} {F : MvPolynomial σ K}
    (hf : ∀ α, vge v a (f α)) (hF : cge v b F) : cge v (a + b) (dg f F) := by sorry

-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_add_fun
-- name    : Formalism.MainNotions.PlaneGram.dg_add_fun
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:06:46.000537+00:00
-- url     : https://prove2.me/theorems/ef47f787-ab91-4c9f-90b9-3ed5fa27d323
-- title:
--   Plane Gram: dg add fun
-- statement:
--   The Plane Gram construction uses the dg add fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L398-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SlopeOfBinomCombGen.lean#L398-L402

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) {σ : Type}
variable {v}
open MvPolynomial

theorem Formalism.MainNotions.PlaneGram.dg_add_fun (f g : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) :
    dg (fun α => f α + g α) F = dg f F + dg g F := by sorry

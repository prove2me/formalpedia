-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_mem_PolK_iff
-- name    : Formalism.MainNotions.PlaneGram.mem_PolK_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:46:00.639471+00:00
-- url     : https://prove2.me/theorems/04971602-f8da-43c2-86c0-372261e691d7
-- title:
--   Plane Gram: mem Pol K iff
-- statement:
--   The Plane Gram construction uses the mem Pol K iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MemPolKIff.lean#L60-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MemPolKIff.lean#L60-L62

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_LiftBoundOfHypotheses
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
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

theorem Formalism.MainNotions.PlaneGram.mem_PolK_iff {L : Type} {r : ℕ} (d : L → ℕ) (F : MvPolynomial (L × Fin r) K) :
    F ∈ PolK K r d ↔ ∀ α ∈ F.support, ∀ i, ldeg α i = d i := by sorry

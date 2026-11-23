-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_mem_initSet
-- name    : Formalism.MainNotions.PlaneGram.mem_initSet
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:39.360114+00:00
-- url     : https://prove2.me/theorems/3278314f-969c-470a-a5ba-fcd2b4b0ebff
-- title:
--   Plane Gram: mem init Set
-- statement:
--   The Plane Gram construction uses the mem init Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingInjective.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingInjective.lean#L9-L10

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_IntegralMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective
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

theorem Formalism.MainNotions.PlaneGram.mem_initSet (N i : ℕ) (k : Fin N) : k ∈ initSet N i ↔ k.val < i := by sorry

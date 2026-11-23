-- Prove2me | Theorems.Thm_Formalism_REAL_compact_highest_weight_unique
-- name    : Formalism.REAL.compact_highest_weight_unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:45:41.288509+00:00
-- url     : https://prove2.me/theorems/0c238294-a3de-4d09-b59c-d73987b46e45
-- title:
--   REAL: compact highest weight unique
-- statement:
--   The REAL construction uses the compact highest weight unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L65-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L65-L87

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

theorem Formalism.REAL.compact_highest_weight_unique (hl : KLow) (hw : KWtOrth) {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} {Λ ν : Fin n → ℝ} {u y : V}
    (hg : GlRel E) (hu : IsUnitary ε E) (hΛ : KHighest ε E Λ u) (hy : y ∈ kSpan ε E u)
    (hyh : KHighest ε E ν y) (hy0 : y ≠ 0) : ν = Λ := by sorry

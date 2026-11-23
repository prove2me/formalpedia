-- Prove2me | Theorems.Thm_Formalism_REAL_compact_span_le_isotypic_part
-- name    : Formalism.REAL.compact_span_le_isotypic_part
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:11.53201+00:00
-- url     : https://prove2.me/theorems/530de732-6d4f-4dbe-92a2-40808385fbcc
-- title:
--   REAL: compact span le isotypic part
-- statement:
--   The REAL construction uses the compact span le isotypic part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L202-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L202-L207

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

theorem Formalism.REAL.compact_span_le_isotypic_part {W : Type} [AddCommGroup W] [Module ℂ W] {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ W} {T : Set (Fin n → ℝ)} {S : Submodule ℂ W} {y : W}
    {μ : Fin n → ℝ} (hy : y ∈ S) (hμ : μ ∈ T) (hyh : KHighest ε F μ y) :
    kSpan ε F y ≤ isoPart ε F T S := by sorry

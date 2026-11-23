-- Prove2me | Theorems.Thm_Formalism_REAL_compact_span_le_of_stable
-- name    : Formalism.REAL.compact_span_le_of_stable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:15.27886+00:00
-- url     : https://prove2.me/theorems/37277d7e-9339-49ac-ae3f-8495736f6a97
-- title:
--   REAL: compact span le of stable
-- statement:
--   The REAL construction uses the compact span le of stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L185-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L185-L188

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

theorem Formalism.REAL.compact_span_le_of_stable {W : Type} [AddCommGroup W] [Module ℂ W] {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ W} {S : Submodule ℂ W} {x : W} (hS : KStable ε F S)
    (hx : x ∈ S) : kSpan ε F x ≤ S := by sorry

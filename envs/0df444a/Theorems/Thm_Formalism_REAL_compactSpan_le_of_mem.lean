-- Prove2me | Theorems.Thm_Formalism_REAL_compactSpan_le_of_mem
-- name    : Formalism.REAL.compactSpan_le_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:19.265057+00:00
-- url     : https://prove2.me/theorems/f760a8b2-7626-4cb1-bab0-011cf63fc94a
-- title:
--   REAL: compact Span le of mem
-- statement:
--   The REAL construction uses the compact Span le of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IsCompactInvariantOrthogonalInf.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IsCompactInvariantOrthogonalInf.lean#L17-L20

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantOrthogonalInf
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

theorem Formalism.REAL.compactSpan_le_of_mem {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) {x : V} {S : Submodule ℂ V} (hx : x ∈ S)
    (hS : KStable ε F S) : kSpan ε F x ≤ S := by sorry

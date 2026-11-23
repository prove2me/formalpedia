-- Prove2me | Theorems.Thm_Formalism_REAL_isCompactInvariant_compactSpan
-- name    : Formalism.REAL.isCompactInvariant_compactSpan
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:37:45.244429+00:00
-- url     : https://prove2.me/theorems/44814648-9dbd-4e67-b968-109613900b3d
-- title:
--   REAL: is Compact Invariant compact Span
-- statement:
--   The REAL construction uses the is Compact Invariant compact Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IsCompactInvariantCompactSpan.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IsCompactInvariantCompactSpan.lean#L20-L24

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantCompactSpan
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
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}

theorem Formalism.REAL.isCompactInvariant_compactSpan (x : V) : KStable ε F (kSpan ε F x) := by sorry

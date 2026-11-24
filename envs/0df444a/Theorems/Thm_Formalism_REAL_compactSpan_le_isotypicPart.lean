-- Prove2me | Theorems.Thm_Formalism_REAL_compactSpan_le_isotypicPart
-- name    : Formalism.REAL.compactSpan_le_isotypicPart
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:20:20.540129+00:00
-- url     : https://prove2.me/theorems/235301a8-c57c-4562-a538-e0f49d896882
-- title:
--   REAL: compact Span le isotypic Part
-- statement:
--   The REAL construction uses the compact Span le isotypic Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IsCompactInvariantOrthogonalInf.lean#L146-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IsCompactInvariantOrthogonalInf.lean#L146-L152

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

theorem Formalism.REAL.compactSpan_le_isotypicPart {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (T : Set (Fin n → ℝ)) (S : Submodule ℂ V) {y : V}
    {μ : Fin n → ℝ} (hy : y ∈ S) (hμ : μ ∈ T) (hk : KHighest ε F μ y) :
    kSpan ε F y ≤ isoPart ε F T S := by sorry

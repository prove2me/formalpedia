-- Prove2me | Theorems.Thm_Formalism_REAL_isCompactInvariant_orthogonal_inf
-- name    : Formalism.REAL.isCompactInvariant_orthogonal_inf
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:23:20.060128+00:00
-- url     : https://prove2.me/theorems/0dbcafe4-4cee-4243-8b8c-c365b015934b
-- title:
--   REAL: is Compact Invariant orthogonal inf
-- statement:
--   The REAL construction uses the is Compact Invariant orthogonal inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IsCompactInvariantOrthogonalInf.lean#L65-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IsCompactInvariantOrthogonalInf.lean#L65-L74

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

theorem Formalism.REAL.isCompactInvariant_orthogonal_inf {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V) (hu : KUnit ε F)
    {K S : Submodule ℂ V} (hK : KStable ε F K) (hS : KStable ε F S) : KStable ε F (Kᗮ ⊓ S) := by sorry

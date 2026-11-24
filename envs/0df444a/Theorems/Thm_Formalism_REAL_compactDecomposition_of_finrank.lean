-- Prove2me | Theorems.Thm_Formalism_REAL_compactDecomposition_of_finrank
-- name    : Formalism.REAL.compactDecomposition_of_finrank
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:20:28.977919+00:00
-- url     : https://prove2.me/theorems/b55117da-c3bc-4dd8-97c9-6eca16e07c32
-- title:
--   REAL: compact Decomposition of finrank
-- statement:
--   The REAL construction uses the compact Decomposition of finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IsCompactInvariantOrthogonalInf.lean#L76-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/IsCompactInvariantOrthogonalInf.lean#L76-L140

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

theorem Formalism.REAL.compactDecomposition_of_finrank (he : KHiExist) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (n : ℕ) (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ V) (hr : KRel ε F)
    (hu : KUnit ε F) :
    ∀ (d : ℕ) (S : Submodule ℂ V), Module.finrank ℂ S = d → FiniteDimensional ℂ S →
    KStable ε F S →
    ∃ (m : ℕ) (x : Fin m → V) (μ : Fin m → Fin n → ℝ),
      (∀ i, x i ∈ S ∧ x i ≠ 0 ∧ KHighest ε F (μ i) (x i)) ∧
      (∀ i i', i ≠ i' → ∀ y ∈ kSpan ε F (x i), ∀ z ∈ kSpan ε F (x i'), ⟪y, z⟫_ℂ = 0) ∧
      (⨆ i, kSpan ε F (x i)) = S := by sorry

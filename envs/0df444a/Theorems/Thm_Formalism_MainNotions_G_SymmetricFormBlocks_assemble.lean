-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_SymmetricFormBlocks_assemble
-- name    : Formalism.MainNotions.G.SymmetricFormBlocks.assemble
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T09:54:46.781428+00:00
-- url     : https://prove2.me/theorems/1b4f7e55-f857-45e9-acd1-b43e27734d23
-- title:
--   Symmetric Form Blocks: assemble
-- statement:
--   The Symmetric Form Blocks construction uses the assemble property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialFactorials/Imports.lean#L7-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialFactorials/Imports.lean#L7-L69

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialFactorials_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.SymmetricFormBlocks
open Finset

theorem Formalism.MainNotions.G.SymmetricFormBlocks.assemble {α ι Z : Type*} (A : Finset α) (Wn : Finset ℕ) (I : Finset Z) (T : Finset ι)
    (bl : α → ℕ → Z → ℝ) (bq : α → Z → ℝ) (dx : Z → ℝ) (dy : α → Z → ℝ) (u : α → ι → α) (m : α → ℝ)
    (ε₁ ε₂ K : ℝ) (h1 : 0 ≤ ε₁) (h2 : 0 ≤ ε₂) (hdx : ∀ z, 0 ≤ dx z)
    (hplus : ∀ a ∈ A, ∀ z ∈ I, ∑ w ∈ Wn, bl a w z ≤ (Wn.card : ℝ) * (bq a z * dx z + ε₂ * (dy a z * dx z)))
    (htm : ∀ z ∈ I, ∑ a ∈ A, bq a z ≤ ε₁ * ∑ i ∈ T, ∑ a ∈ A, dy (u a i) z)
    (hcnt : ∀ a ∈ A, ∑ z ∈ I, dy a z * dx z ≤ m a)
    (hu : ∀ a ∈ A, ∀ i ∈ T, u a i ∈ A ∧ m (u a i) ≤ K * m a) :
    ∑ a ∈ A, ∑ w ∈ Wn, ∑ z ∈ I, bl a w z ≤ (ε₁ * T.card * K + ε₂) * ((Wn.card : ℝ) * ∑ a ∈ A, m a) := by sorry

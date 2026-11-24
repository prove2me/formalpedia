-- Prove2me | Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_QuadraticBasis_oIso
-- name    : Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.oIso
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:12:34.183462+00:00
-- url     : https://prove2.me/theorems/dd893599-f1c3-45ed-9aaa-8f9782ac9737
-- title:
--   Quadratic Basis: o Iso
-- statement:
--   The Quadratic Basis construction uses the o Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/QuadraticBasis/FinalO.lean#L6-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/QuadraticBasis/FinalO.lean#L6-L8

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_QuadRoots
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_OIsoOf
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_FinalO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis

theorem Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.oIso (p n' : ℕ) (hp : p.Prime) (hn : 0 < n') (W₁ W₂ O₁ O₂ : Type) [CommRing W₁] [IsDomain W₁] [IsDiscreteValuationRing W₁] [CommRing W₂] [IsDomain W₂] [IsDiscreteValuationRing W₂] [CommRing O₁] [IsDomain O₁] [IsDiscreteValuationRing O₁] [CommRing O₂] [IsDomain O₂] [IsDiscreteValuationRing O₂] (j₁ : W₁ →+* O₁) (j₂ : W₂ →+* O₂) (w₁ : O₁) (w₂ : O₂)
 (a₁ : Irreducible (p : W₁)) (a₂ : Irreducible (p : W₂)) (b₁ : Nat.card (W₁ ⧸ Ideal.span {(p : W₁)}) = p ^ n') (b₂ : Nat.card (W₂ ⧸ Ideal.span {(p : W₂)}) = p ^ n') (c₁ : IsAdicComplete (Ideal.span {(p : W₁)}) W₁) (c₂ : IsAdicComplete (Ideal.span {(p : W₂)}) W₂) (d₁ : j₁.Finite) (d₂ : j₂.Finite) (e₁ : IsAdicComplete (IsLocalRing.maximalIdeal O₁) O₁) (e₂ : IsAdicComplete (IsLocalRing.maximalIdeal O₂) O₂) (f₁ : w₁ ^ 2 = (p : O₁)) (f₂ : w₂ ^ 2 = (p : O₂)) (g₁ : Irreducible w₁) (g₂ : Irreducible w₂) (h₁ : Nat.card (O₁ ⧸ Ideal.span {w₁}) = p ^ (2 * n')) (h₂ : Nat.card (O₂ ⧸ Ideal.span {w₂}) = p ^ (2 * n')) (φW : W₁ ≃+* W₂) : ∃ φO : O₁ ≃+* O₂, (∀ x, φO (j₁ x) = j₂ (φW x)) ∧ φO w₁ = w₂ := by sorry

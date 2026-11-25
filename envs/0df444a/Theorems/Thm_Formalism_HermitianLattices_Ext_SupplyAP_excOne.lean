-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_excOne
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.excOne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:59:00.495555+00:00
-- url     : https://prove2.me/theorems/b32eddd7-4f52-477d-9af5-f570ecce2295
-- title:
--   Supply AP: exc One
-- statement:
--   The Supply AP construction uses the exc One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/ExcOne.lean#L9-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/ExcOne.lean#L9-L29

import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_ExcOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.ZeroFreeDirichlet
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP

theorem Formalism.HermitianLattices.Ext.SupplyAP.excOne : ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 20 ∧
    ∀ (m : ℕ) [NeZero m], ∃ B : DirichletCharacter ℂ m → Finset ℝ,
      (∀ χ, ExcZeros c₁ χ (B χ)) ∧
      (∀ χ χ', (B χ).Nonempty → (B χ').Nonempty → χ = χ') ∧
      (∀ χ, ∀ β ∈ B χ, χ ^ 2 = 1 ∧ χ ≠ 1 ∧ 1 / 2 ≤ β ∧
        DirichletCharacter.LFunction χ (β : ℂ) = 0) := by sorry

-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_psiAPLowerOf
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.psiAPLowerOf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:02.27445+00:00
-- url     : https://prove2.me/theorems/9f089a96-21c8-4625-a29d-9c3e1c125b16
-- title:
--   Supply AP: psi APLower Of
-- statement:
--   The Supply AP construction uses the psi APLower Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffPsi.lean#L83-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffPsi.lean#L83-L159

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_ExcOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_ExcTerm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffBase
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffPsi
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

theorem Formalism.HermitianLattices.Ext.SupplyAP.psiAPLowerOf (A : ℕ) (hA : ExcBoundAt A) : ∃ c c₀ C : ℝ, 0 < c ∧ 0 < c₀ ∧ 0 ≤ C ∧
    ∀ (m a : ℕ) (x : ℝ), 1 ≤ m → Nat.Coprime a m → 0 < x → 4 ≤ Real.log x →
      (m : ℝ) ≤ Real.exp (c * Real.sqrt (Real.log x)) →
      c₀ * x / (m : ℝ) ^ (A + 1) - C * x * Real.exp (-c * Real.sqrt (Real.log x)) ≤ psiAP m a x := by sorry

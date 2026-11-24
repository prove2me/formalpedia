-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_smoothLower
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.smoothLower
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:14.923115+00:00
-- url     : https://prove2.me/theorems/b8b8913c-2cae-4025-b885-4ad1144dc30b
-- title:
--   Supply AP: smooth Lower
-- statement:
--   The Supply AP construction uses the smooth Lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffSmooth.lean#L230-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffSmooth.lean#L230-L269

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffBase
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
open Finset
open scoped ComplexOrder

theorem Formalism.HermitianLattices.Ext.SupplyAP.smoothLower (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1)
    (K N : ℕ) (x : ℝ) (hx : 0 < x) (hKx : (K : ℝ) ^ 2 ≤ x) (hKN : K ^ 2 ≤ N) :
    (K : ℝ) / Real.exp 1 ≤
      x * (∑ d ∈ Finset.Icc 1 N, χ (d : ZMod q) / (d : ℂ)).re +
      (∑ d ∈ Finset.Icc 1 N, χ (d : ZMod q) * ((gExp ((d : ℝ) / x) : ℝ) : ℂ)).re +
      (N : ℝ) * (x + 1) * Real.exp (-(N : ℝ) / x) := by sorry

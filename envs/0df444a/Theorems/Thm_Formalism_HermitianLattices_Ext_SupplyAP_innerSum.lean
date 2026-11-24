-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_innerSum
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.innerSum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:12.557293+00:00
-- url     : https://prove2.me/theorems/93e80045-8fc6-4c5b-b36c-e881b66ac1bb
-- title:
--   Supply AP: inner Sum
-- statement:
--   The Supply AP construction uses the inner Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffSmooth.lean#L60-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffSmooth.lean#L60-L122

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

theorem Formalism.HermitianLattices.Ext.SupplyAP.innerSum (x : ℝ) (hx : 0 < x) (d N : ℕ) (hd : 1 ≤ d) :
    ∃ T : ℝ, 0 ≤ T ∧ T ≤ (x + 1) * Real.exp (-(N : ℝ) / x) ∧
      ∑ m ∈ Icc 1 (N / d), Real.exp (-((d * m : ℕ) : ℝ) / x) = x / d + gExp ((d : ℝ) / x) - T := by sorry

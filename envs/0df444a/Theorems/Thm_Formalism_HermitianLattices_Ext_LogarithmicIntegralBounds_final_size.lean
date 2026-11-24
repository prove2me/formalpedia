-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_final_size
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.final_size
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:53.085609+00:00
-- url     : https://prove2.me/theorems/fcbe8b9e-ddc3-4cc3-8ca8-3f5f4df0a1c7
-- title:
--   Logarithmic Integral Bounds: final size
-- statement:
--   The Logarithmic Integral Bounds construction uses the final size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqMainB.lean#L72-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqMainB.lean#L72-L171

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqMainB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.final_size (ε : ℝ) (hε1 : ε ≤ 1) (x : ℝ) (hx3 : 3 ≤ x) (C1 C2 C3 C4 S1 Sd R : ℝ)
    (hS0 : 0 ≤ S1) (hS1 : S1 ≤ C1 * x * Real.log x) (hSd : Sd ≤ C4 * x * Real.log x) (hR0 : 0 ≤ R)
    (hR : R ≤ C3 * (Real.sqrt x + x ^ (ε / 5) * Real.log x)) :
    Sd + R ^ 2 + (2 * (|C2| * Real.log x) ^ 2 + 2 * (|C2| * Real.log x) * R) + x ^ (-3 : ℝ) * S1 ^ 2 ≤
      (|C4| + 25 * C3 ^ 2 + 2 * C2 ^ 2 + 10 * |C2| * |C3| + C1 ^ 2) * x * Real.log x := by sorry

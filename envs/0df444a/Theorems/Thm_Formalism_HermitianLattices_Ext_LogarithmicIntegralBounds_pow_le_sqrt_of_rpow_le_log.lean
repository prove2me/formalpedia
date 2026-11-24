-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_pow_le_sqrt_of_rpow_le_log
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.pow_le_sqrt_of_rpow_le_log
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:00.718648+00:00
-- url     : https://prove2.me/theorems/234af3e9-04d5-4a13-8353-947e558f482b
-- title:
--   Logarithmic Integral Bounds: pow le sqrt of rpow le log
-- statement:
--   The Logarithmic Integral Bounds construction uses the pow le sqrt of rpow le log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqMainB.lean#L38-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqMainB.lean#L38-L70

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.pow_le_sqrt_of_rpow_le_log (ε : ℝ) (hε : 0 < ε) (x X : ℝ) (hx3 : 3 ≤ x) (hx : (19200 / ε) ^ (12 / ε) ≤ x)
    (hX : 0 < X) (hlog : x ^ (ε / 6) ≤ Real.log X) : x ^ 800 ≤ X ^ (1 / 2 : ℝ) := by sorry

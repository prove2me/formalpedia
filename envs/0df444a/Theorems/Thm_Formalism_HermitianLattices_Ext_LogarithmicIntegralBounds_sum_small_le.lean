-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_sum_small_le
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.sum_small_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:16.100334+00:00
-- url     : https://prove2.me/theorems/35cdd24c-c971-47ee-bb16-e6c9afdecb52
-- title:
--   Logarithmic Integral Bounds: sum small le
-- statement:
--   The Logarithmic Integral Bounds construction uses the sum small le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqTwistA.lean#L107-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqTwistA.lean#L107-L125

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqOrth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistA
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
open Formalism.HermitianLattices.ZeroFreeRegionGL2

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.sum_small_le (m₀ s a₀ : ℕ) (X : ℝ) (hX : 0 ≤ X) :
    (∑ b ∈ clsB m₀ s a₀, (smallCnt X (m₀ * s) b : ℝ)) ≤ X ^ (1 / 2 : ℝ) := by sorry

-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Fm_parts
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Fm_parts
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:53:02.408271+00:00
-- url     : https://prove2.me/theorems/adf9d573-0289-4903-adc4-f27f96a7630d
-- title:
--   Primes In Progressions: Fm parts
-- statement:
--   The Primes In Progressions construction uses the Fm parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiB.lean#L132-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiB.lean#L132-L167

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistC
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiB
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Fm_parts (K θ : ℝ) {β X : ℝ} (hβ : 0 < β) (hX : 2 ≤ X) :
    Fm K θ β X / Real.log X + ∫ t in (2 : ℝ)..X, Fm K θ β t / (t * Real.log t ^ 2) =
      Fm K θ β 2 / Real.log 2 + K * (liX X - θ * (liX (X ^ β) - liX ((2 : ℝ) ^ β))) := by sorry

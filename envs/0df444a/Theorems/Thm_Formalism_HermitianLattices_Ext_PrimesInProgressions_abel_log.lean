-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_abel_log
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.abel_log
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:53:20.323135+00:00
-- url     : https://prove2.me/theorems/9df172fa-4574-4406-9efe-3f9bee7c9b8c
-- title:
--   Primes In Progressions: abel log
-- statement:
--   The Primes In Progressions construction uses the abel log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiB.lean#L13-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiB.lean#L13-L33

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.abel_log (c : ℕ → ℝ) (h0 : c 0 = 0) (h1 : c 1 = 0) {X : ℝ} (hX : 2 ≤ X) :
    ∑ n ∈ Icc 0 ⌊X⌋₊, (Real.log n)⁻¹ * c n = (∑ n ∈ Icc 0 ⌊X⌋₊, c n) / Real.log X +
      ∫ t in (2 : ℝ)..X, (∑ n ∈ Icc 0 ⌊t⌋₊, c n) / (t * Real.log t ^ 2) := by sorry

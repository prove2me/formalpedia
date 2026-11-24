-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhpr_blocks
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.dhpr_blocks
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:24.47637+00:00
-- url     : https://prove2.me/theorems/d35e63d5-99ae-4e68-a840-fc396d226b3e
-- title:
--   Primes In Progressions: dhpr blocks
-- statement:
--   The Primes In Progressions construction uses the dhpr blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHPrimeB.lean#L212-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHPrimeB.lean#L212-L221

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPrimeB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.dhpr_blocks (g : ℕ → ℝ) (v0 : ℕ) : ∀ V, v0 ≤ V →
    ∑ n ∈ Ioc ⌊Real.exp (v0 : ℝ)⌋₊ ⌊Real.exp (V : ℝ)⌋₊, g n =
      ∑ v ∈ Ico v0 V, ∑ n ∈ Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊, g n := by sorry

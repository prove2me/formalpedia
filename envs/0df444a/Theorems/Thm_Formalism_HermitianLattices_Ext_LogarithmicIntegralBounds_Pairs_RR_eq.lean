-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_RR_eq
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.RR_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:18:01.325807+00:00
-- url     : https://prove2.me/theorems/4ba9944d-e866-485c-a0dd-e712a03d7f60
-- title:
--   Pairs: RR eq
-- statement:
--   The Pairs construction uses the RR eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPairs.lean#L90-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPairs.lean#L90-L91

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqPairs
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
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.RR_eq (c : ℕ → ℝ) (m₀ N : ℕ) : RR c m₀ N = ∑ n ∈ Icc 1 N, gW c m₀ n := by sorry

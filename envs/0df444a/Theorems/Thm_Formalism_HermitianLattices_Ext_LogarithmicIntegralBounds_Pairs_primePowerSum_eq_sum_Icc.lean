-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_primePowerSum_eq_sum_Icc
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.primePowerSum_eq_sum_Icc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:32.856809+00:00
-- url     : https://prove2.me/theorems/8cb5c162-039f-4634-aabd-a943217b76c2
-- title:
--   Pairs: prime Power Sum eq sum Icc
-- statement:
--   The Pairs construction uses the prime Power Sum eq sum Icc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPairs.lean#L87-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPairs.lean#L87-L88

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.primePowerSum_eq_sum_Icc (c : ℕ → ℝ) (N p : ℕ) : sP c N p = ∑ n ∈ Icc 1 N, aW c p n := by sorry

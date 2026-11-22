-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_dbl_sum
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.dbl_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:49.956923+00:00
-- url     : https://prove2.me/theorems/72fddad4-4052-4edb-af00-54eef58fc3fe
-- title:
--   Pairs: dbl sum
-- statement:
--   The Pairs construction uses the dbl sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPairs.lean#L130-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPairs.lean#L130-L132

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.dbl_sum (s : Finset ℕ) (f g : ℕ → ℝ) :
    ∑ n ∈ s, ∑ n' ∈ s, f n * g n' = (∑ n ∈ s, f n) * ∑ n ∈ s, g n := by sorry

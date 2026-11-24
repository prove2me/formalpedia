-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_pairs_r
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.pairs_r
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:57.356925+00:00
-- url     : https://prove2.me/theorems/7a4846d8-bd8b-49d3-bff9-09a78209f285
-- title:
--   Logarithmic Integral Bounds: pairs r
-- statement:
--   The Logarithmic Integral Bounds construction uses the pairs r property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPairs.lean#L307-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPairs.lean#L307-L323

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
open Pairs

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.pairs_r (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hpp : ∀ n, c n ≠ 0 → IsPrimePow n) (m₀ N r : ℕ) (hr : 1 < r)
    (B : ℝ) (hB : ∀ p, sP c N p ≤ B) :
    (∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, if soutPart m₀ (n * n') = r then c n * c n' else 0) ≤
      2 * B ^ 2 + 2 * B * RR c m₀ N := by sorry

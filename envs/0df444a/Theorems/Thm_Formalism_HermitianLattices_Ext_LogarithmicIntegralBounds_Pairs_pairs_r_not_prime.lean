-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_pairs_r_not_prime
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.pairs_r_not_prime
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:23.459519+00:00
-- url     : https://prove2.me/theorems/62dca74e-e41b-4eb0-9f0b-28f7783b04ae
-- title:
--   Pairs: pairs r not prime
-- statement:
--   The Pairs construction uses the pairs r not prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPairs.lean#L195-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPairs.lean#L195-L249

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.pairs_r_not_prime (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hpp : ∀ n, c n ≠ 0 → IsPrimePow n) (m₀ N r : ℕ)
    (hr : 1 < r) (hrp : ¬ r.Prime) :
    (∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, if soutPart m₀ (n * n') = r then c n * c n' else 0) ≤
      sP c N r.minFac * sP c N (r / r.minFac) + sP c N (r / r.minFac) * sP c N r.minFac := by sorry

-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_pow_absorb
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.pow_absorb
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:19:25.521727+00:00
-- url     : https://prove2.me/theorems/e1d5f6d3-60aa-4b1e-b66b-e7bcea8acbf9
-- title:
--   Primes In Progressions: pow absorb
-- statement:
--   The Primes In Progressions construction uses the pow absorb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTZSumL.lean#L12-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTZSumL.lean#L12-L28

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHBSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTZSum
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTZSumL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.pow_absorb (N : ℕ) (c l large₂ : ℝ) (hc : 0 < c) (hl : 2 ≤ l)
    (hL : 2 * N / c * l * Real.log (l + 2) ≤ large₂) :
    l ^ N * Real.exp (-(c / 2 * large₂ / l)) ≤ 1 := by sorry

-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exp_sum_le_min_exponent
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.exp_sum_le_min_exponent
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:27:06.345869+00:00
-- url     : https://prove2.me/theorems/01f07d26-248f-5c1f-beb1-3aaa35cd7577
-- title:
--   Primes In Progressions: exp sum le min exponent
-- statement:
--   The Primes In Progressions construction uses the exp sum le min exponent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiC.lean#L53-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiC.lean#L53-L72

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiC
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
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet ArithmeticFunction

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.exp_sum_le_min_exponent {c l L u : ℝ} (hc : 0 < c) (hl : 0 < l) (hL : 0 ≤ L) (hu : L / 2 ≤ u) :
    Real.exp (-(c * u / l)) + Real.exp (-(c * Real.sqrt u)) ≤
      Real.exp (-(min (c / 2) (c ^ 2 / 2) * L / l)) + Real.exp (-Real.sqrt (min (c / 2) (c ^ 2 / 2) * L)) := by sorry

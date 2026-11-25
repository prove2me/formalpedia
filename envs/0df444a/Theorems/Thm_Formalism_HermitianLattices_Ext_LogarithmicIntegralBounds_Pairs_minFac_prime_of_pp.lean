-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_minFac_prime_of_pp
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.minFac_prime_of_pp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:40:21.938931+00:00
-- url     : https://prove2.me/theorems/b4353a29-d55a-5d70-9e31-36dbc8570856
-- title:
--   Pairs: min Fac prime of pp
-- statement:
--   The Pairs construction uses the min Fac prime of pp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPairs.lean#L128-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPairs.lean#L128-L128

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.minFac_prime_of_pp {n : ℕ} (h : IsPrimePow n) : n.minFac.Prime := by sorry

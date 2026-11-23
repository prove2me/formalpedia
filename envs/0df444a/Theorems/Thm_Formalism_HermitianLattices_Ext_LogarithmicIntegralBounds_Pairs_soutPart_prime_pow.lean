-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_soutPart_prime_pow
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.soutPart_prime_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:18:13.347578+00:00
-- url     : https://prove2.me/theorems/263e4190-94eb-489c-8797-faf2b9b8c7b9
-- title:
--   Pairs: sout Part prime pow
-- statement:
--   The Pairs construction uses the sout Part prime pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPairs.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPairs.lean#L15-L19

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.soutPart_prime_pow (m₀ p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    soutPart m₀ (p ^ k) = if Odd k ∧ ¬ p ∣ m₀ then p else 1 := by sorry

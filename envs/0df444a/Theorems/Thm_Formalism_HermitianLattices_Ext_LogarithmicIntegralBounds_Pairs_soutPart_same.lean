-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_soutPart_same
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.soutPart_same
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:18:09.664708+00:00
-- url     : https://prove2.me/theorems/ec413c82-2ee8-4a35-bf6b-59737f9d0d65
-- title:
--   Pairs: sout Part same
-- statement:
--   The Pairs construction uses the sout Part same property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPairs.lean#L54-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPairs.lean#L54-L61

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.soutPart_same {m₀ n n' : ℕ} (h : IsPrimePow n) (h' : IsPrimePow n') (he : n.minFac = n'.minFac) :
    soutPart m₀ (n * n') = 1 ∨ soutPart m₀ (n * n') = n.minFac := by sorry

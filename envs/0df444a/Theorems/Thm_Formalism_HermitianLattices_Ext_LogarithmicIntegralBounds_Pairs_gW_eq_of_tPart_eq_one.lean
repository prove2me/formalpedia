-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_gW_eq_of_tPart_eq_one
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.gW_eq_of_tPart_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:18:36.061082+00:00
-- url     : https://prove2.me/theorems/85bfb5cf-be2f-483c-9815-5f5516145777
-- title:
--   Pairs: g W eq of t Part eq one
-- statement:
--   The Pairs construction uses the g W eq of t Part eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPairs.lean#L115-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqPairs.lean#L115-L122

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.gW_eq_of_tPart_eq_one {c : ℕ → ℝ} {m₀ n : ℕ} (h : IsPrimePow n) (ht : tPart m₀ n = 1) : gW c m₀ n = c n := by sorry

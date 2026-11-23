-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhpr_one_sub_exp_neg
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.dhpr_one_sub_exp_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:19:41.387414+00:00
-- url     : https://prove2.me/theorems/97c6b58a-1ae5-482f-afb0-d35454c109a4
-- title:
--   Primes In Progressions: dhpr one sub exp neg
-- statement:
--   The Primes In Progressions construction uses the dhpr one sub exp neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHPrimeB.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHPrimeB.lean#L23-L31

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPrimeB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.dhpr_one_sub_exp_neg {a : ℝ} (ha : 0 < a) : a / (1 + a) ≤ 1 - Real.exp (-a) := by sorry

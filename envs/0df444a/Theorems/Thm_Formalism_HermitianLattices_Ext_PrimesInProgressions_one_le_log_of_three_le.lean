-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_one_le_log_of_three_le
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.one_le_log_of_three_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:19:53.74714+00:00
-- url     : https://prove2.me/theorems/c96c497c-99ff-40e3-9d05-3141123aa78c
-- title:
--   Primes In Progressions: one le log of three le
-- statement:
--   The Primes In Progressions construction uses the one le log of three le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsmA.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsmA.lean#L57-L60

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTBAsmA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.one_le_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by sorry

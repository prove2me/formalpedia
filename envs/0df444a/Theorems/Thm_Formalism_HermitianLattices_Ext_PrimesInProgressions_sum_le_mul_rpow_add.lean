-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_sum_le_mul_rpow_add
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.sum_le_mul_rpow_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:38.004929+00:00
-- url     : https://prove2.me/theorems/31766a23-afb9-4882-aa7a-247b29e218cc
-- title:
--   Primes In Progressions: sum le mul rpow add
-- statement:
--   The Primes In Progressions construction uses the sum le mul rpow add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplMainA.lean#L238-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplMainA.lean#L238-L249

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplMainA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.sum_le_mul_rpow_add (AL AW C X Y W : ℝ) (hC4 : 4 ≤ C) (hCL : AL ≤ C) (hCW : AW ≤ C) (hX : 1 ≤ X)
    (hY : 0 ≤ Y) (hW : 0 ≤ W) : AL * (X ^ 4 * Y) + AW * W ≤ C * (X ^ C * Y + W) := by sorry

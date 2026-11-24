-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_DHF_pow_small_a
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.pow_small_a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:34.002745+00:00
-- url     : https://prove2.me/theorems/2519d181-116d-4d11-a450-eb71f995242f
-- title:
--   DHF: pow small a
-- statement:
--   The DHF construction uses the pow small a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHFinishA.lean#L121-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHFinishA.lean#L121-L138

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHFinishA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.pow_small_a (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (K : ℕ) (hK3 : 3 ≤ K) :
    (K : ℝ) * (q ^ 2 / 8) ^ (K - 1) ≤ q ^ K / 8 := by sorry

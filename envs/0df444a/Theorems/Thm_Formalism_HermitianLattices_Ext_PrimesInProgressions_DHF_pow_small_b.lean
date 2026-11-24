-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_DHF_pow_small_b
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.pow_small_b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:36.184797+00:00
-- url     : https://prove2.me/theorems/cd424f8d-fc6b-4941-b10b-12fa57229854
-- title:
--   DHF: pow small b
-- statement:
--   The DHF construction uses the pow small b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHFinishA.lean#L140-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHFinishA.lean#L140-L153

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.pow_small_b (q : ℝ) (hq0 : 0 ≤ q) (K : ℕ) (hK3 : 3 ≤ K) :
    (K : ℝ) * (q / 4) ^ K ≤ q ^ K / 8 := by sorry

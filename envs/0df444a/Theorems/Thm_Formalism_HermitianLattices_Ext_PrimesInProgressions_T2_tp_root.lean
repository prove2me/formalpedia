-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_tp_root
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.tp_root
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:17.816844+00:00
-- url     : https://prove2.me/theorems/178bda18-eb77-4c47-b4dc-a2cba7c2a20b
-- title:
--   T2: tp root
-- statement:
--   The T2 construction uses the tp root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TpCoeffNorm.lean#L73-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TpCoeffNorm.lean#L73-L76

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TpCoeffNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Polynomial
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.T2

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.tp_root (n : ℕ) (z : Fin n → ℂ) (i : Fin n) :
    ∑ a ∈ range (n + 1), (tp n z).coeff a * z i ^ a = 0 := by sorry

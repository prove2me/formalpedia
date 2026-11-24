-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_tp_rev
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.tp_rev
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:10.809763+00:00
-- url     : https://prove2.me/theorems/562f38ac-827e-4ba4-9840-d11522af68e8
-- title:
--   T2: tp rev
-- statement:
--   The T2 construction uses the tp rev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TpCoeffNorm.lean#L60-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/TpCoeffNorm.lean#L60-L71

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.tp_rev (n : ℕ) (z : Fin n → ℂ) (ζ : ℂ) (hζ : ζ ≠ 0) :
    ∏ i, (1 - z i * ζ) = ∑ a ∈ range (n + 1), (tp n z).coeff a * ζ ^ (n - a) := by sorry

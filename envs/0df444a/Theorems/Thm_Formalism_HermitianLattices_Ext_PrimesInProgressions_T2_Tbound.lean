-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_Tbound
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.Tbound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:59.947989+00:00
-- url     : https://prove2.me/theorems/ef4981b4-a458-4f95-b057-a16943310a44
-- title:
--   T2: Tbound
-- statement:
--   The T2 construction uses the Tbound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/HDSucc.lean#L28-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/HDSucc.lean#L28-L110

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TpCoeffNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_HDSucc
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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.Tbound (n m : ℕ) (hn : 1 ≤ n) (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) (β : ℝ)
    (hβ : ∀ k, m + 1 ≤ k → k ≤ m + n → ‖∑ i, z i ^ k‖ ≤ β) (ζ : ℂ) (hζ1 : 1 ≤ ‖ζ‖)
    (hne : ∀ i, 1 - z i * ζ ≠ 0) :
    ‖∏ i, (1 - z i * ζ)‖ * ‖∑ i, (z i * ζ) ^ (m + 1) / (1 - z i * ζ)‖ ≤
      ‖ζ‖ ^ (m + 1) * (n * (‖ζ‖ ^ n * (2 ^ n * β))) := by sorry

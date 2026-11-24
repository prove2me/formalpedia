-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_hD_tele
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.hD_tele
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:58.742663+00:00
-- url     : https://prove2.me/theorems/38fa684c-1fa9-4a68-851a-f13bcb5883da
-- title:
--   T2: h D tele
-- statement:
--   The T2 construction uses the h D tele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/HDSucc.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/HDSucc.lean#L19-L26

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.hD_tele (φ : ℕ → ℂ) (x ζ : ℂ) (K : ℕ) :
    (1 - x * ζ) * ∑ b ∈ range (K + 1), hD φ x b * ζ ^ b =
      ∑ b ∈ range (K + 1), φ b * ζ ^ b - x * hD φ x K * ζ ^ (K + 1) := by sorry

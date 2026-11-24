-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_prodLower
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.prodLower
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:39.61066+00:00
-- url     : https://prove2.me/theorems/f17d9160-d632-48b5-baf2-54cdcf98eec9
-- title:
--   T2: prod Lower
-- statement:
--   The T2 construction uses the prod Lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/Turan2Main.lean#L11-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/Turan2Main.lean#L11-L27

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExistsFarFromPoints
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_RootNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_HDSucc
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_Turan2Main
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.T2

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.prodLower (n : ℕ) (z : Fin n → ℂ) (ρ : ℝ) (hρ : 0 < ρ) (ξ : ℂ) (hξ : ‖ξ‖ = ρ⁻¹) :
    ρ⁻¹ ^ n * ∏ i, |ρ - ‖z i‖| ≤ ‖∏ i, (1 - z i * ξ)‖ := by sorry

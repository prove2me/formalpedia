-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_turan2Main
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.turan2Main
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:44.92261+00:00
-- url     : https://prove2.me/theorems/e8e1cfc9-7534-4916-981a-927646334953
-- title:
--   T2: turan2 Main
-- statement:
--   The T2 construction uses the turan2 Main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/Turan2Main.lean#L29-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/Turan2Main.lean#L29-L174

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.turan2Main (n m : ℕ) (z : Fin n → ℂ) (hn : 1 ≤ n) (hz : ∀ i, ‖z i‖ ≤ 1) (hz1 : ∃ i, ‖z i‖ = 1) :
    ∃ k : ℕ, m + 1 ≤ k ∧ k ≤ m + n ∧ ((n : ℝ) / (1600 * ((m : ℝ) + n))) ^ n ≤ ‖∑ i, z i ^ k‖ := by sorry

-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_exists_far_from_points
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.exists_far_from_points
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:14.338777+00:00
-- url     : https://prove2.me/theorems/9ac77a3b-bee6-4707-b1ca-6d2992ffc5c9
-- title:
--   T2: exists far from points
-- statement:
--   The T2 construction uses the exists far from points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExistsFarFromPoints.lean#L92-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExistsFarFromPoints.lean#L92-L117

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExistsFarFromPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.T2

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.exists_far_from_points {ι : Type*} [DecidableEq ι] (t : ι → ℝ) :
    ∀ (N : ℕ) (s : Finset ι), s.card = N → ∀ (c r : ℝ), 0 < r →
      ∃ ρ : ℝ, |ρ - c| ≤ r ∧ (r / 25) ^ s.card ≤ ∏ j ∈ s, |ρ - t j| := by sorry

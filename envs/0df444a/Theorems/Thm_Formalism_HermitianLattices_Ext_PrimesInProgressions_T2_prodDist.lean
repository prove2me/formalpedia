-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_prodDist
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.prodDist
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:53:09.688804+00:00
-- url     : https://prove2.me/theorems/e9e8ee56-6e06-4430-936f-bd6510cb4c52
-- title:
--   T2: prod Dist
-- statement:
--   The T2 construction uses the prod Dist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExistsFarFromPoints.lean#L119-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExistsFarFromPoints.lean#L119-L121

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.prodDist {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (s : Finset ι) (c r : ℝ) (hr : 0 < r) :
    ∃ ρ : ℝ, |ρ - c| ≤ r ∧ (r / 25) ^ s.card ≤ ∏ j ∈ s, |ρ - t j| := by sorry

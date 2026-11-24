-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_prodDist_step
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.prodDist_step
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:58.161632+00:00
-- url     : https://prove2.me/theorems/37bc78a1-669b-47c4-a8ed-143220e0041e
-- title:
--   T2: prod Dist step
-- statement:
--   The T2 construction uses the prod Dist step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExistsFarFromPoints.lean#L20-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExistsFarFromPoints.lean#L20-L46

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.prodDist_step {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (s S : Finset ι) (hS : S ⊆ s)
    (h3 : 3 * S.card ≤ s.card) (r ρ : ℝ) (hr : 0 < r)
    (hfar : ∀ j ∈ s, j ∉ S → r / 5 ≤ |ρ - t j|)
    (hin : ((r / 5) / 25) ^ S.card ≤ ∏ j ∈ S, |ρ - t j|) :
    (r / 25) ^ s.card ≤ ∏ j ∈ s, |ρ - t j| := by sorry

-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_differenced_kernel_bound
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.differenced_kernel_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:24.528503+00:00
-- url     : https://prove2.me/theorems/44191079-8294-483d-ba6e-de2de4cfaa9a
-- title:
--   Primes In Progressions: differenced kernel bound
-- statement:
--   The Primes In Progressions construction uses the differenced kernel bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTSharpA.lean#L26-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTSharpA.lean#L26-L60

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTSharpA
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.differenced_kernel_bound {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) (hre : ρ.re ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    ‖(((1 + δ : ℝ) : ℂ) ^ (ρ - 1) - 1) / (ρ - 1) + (((1 + δ)⁻¹ - 1 : ℝ) : ℂ)‖ ≤ ‖ρ‖ * δ * δ := by sorry

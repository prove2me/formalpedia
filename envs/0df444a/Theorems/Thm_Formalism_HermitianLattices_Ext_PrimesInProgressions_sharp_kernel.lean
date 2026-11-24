-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_sharp_kernel
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.sharp_kernel
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:35.326794+00:00
-- url     : https://prove2.me/theorems/c20cab29-c1b6-4985-b536-078273a9bdd0
-- title:
--   Primes In Progressions: sharp kernel
-- statement:
--   The Primes In Progressions construction uses the sharp kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTSharpA.lean#L62-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTSharpA.lean#L62-L81

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.sharp_kernel {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) (hre : ρ.re ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) :
    ‖(((1 + δ) / δ : ℝ) : ℂ) * ((((1 + δ : ℝ) : ℂ) ^ (ρ - 1) - 1) / (ρ - 1)) - 1‖ ≤ 2 * δ * ‖ρ‖ := by sorry

-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_bdry_ne
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_bdry_ne
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:50:33.395056+00:00
-- url     : https://prove2.me/theorems/b6449e12-80d9-40ba-89f0-dd5f5fee496e
-- title:
--   Primes In Progressions: ex bdry ne
-- statement:
--   The Primes In Progressions construction uses the ex bdry ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplRectF.lean#L137-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplRectF.lean#L137-L146

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRect
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRectF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_bdry_ne {x₀ x₁ y₀ y₁ : ℝ} (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) (hx₁ : 1 < x₁)
    (hy₀ : y₀ < 0) (hy₁ : 0 < y₁) {w : ℂ} (hw : w ∈ exBdry x₀ x₁ y₀ y₁) : w ≠ 0 ∧ w ≠ 1 := by sorry

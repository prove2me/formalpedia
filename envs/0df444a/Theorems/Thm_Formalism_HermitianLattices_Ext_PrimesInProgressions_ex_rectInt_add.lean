-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_rectInt_add
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_rectInt_add
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:49:32.406574+00:00
-- url     : https://prove2.me/theorems/d386ccd9-32ce-5b7b-87d2-59fe960aaeec
-- title:
--   Primes In Progressions: ex rect Int add
-- statement:
--   The Primes In Progressions construction uses the ex rect Int add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplRectF.lean#L117-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplRectF.lean#L117-L126

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_rectInt_add {f g : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hf : ContinuousOn f (exBdry x₀ x₁ y₀ y₁)) (hg : ContinuousOn g (exBdry x₀ x₁ y₀ y₁)) :
    Formalism.ZF.rectInt (fun w => f w + g w) x₀ x₁ y₀ y₁ =
      Formalism.ZF.rectInt f x₀ x₁ y₀ y₁ + Formalism.ZF.rectInt g x₀ x₁ y₀ y₁ := by sorry

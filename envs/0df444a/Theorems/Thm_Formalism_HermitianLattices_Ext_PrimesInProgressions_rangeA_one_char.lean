-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_rangeA_one_char
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.rangeA_one_char
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:18:15.466551+00:00
-- url     : https://prove2.me/theorems/39eb3e2a-710f-4c6f-a263-28f767959be7
-- title:
--   Primes In Progressions: range A one char
-- statement:
--   The Primes In Progressions construction uses the range A one char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTRangeA.lean#L93-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTRangeA.lean#L93-L159

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTRangeA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.rangeA_one_char (c C cA : ℝ)
    (H : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (B : Finset ℝ) (x : ℝ), ExcZeros cZ χ B → 2 ≤ x →
      (q : ℝ) ≤ Real.exp (c * Real.sqrt (Real.log x)) →
      ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0) + ∑ β ∈ B, (x : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)))
    (hcA : cA ≤ cZ) (hcA' : cA ≤ c) (M : ℕ) [NeZero M] (hM : 8 ≤ M) (y : ℝ) (hy : 2 ≤ y)
    (hl : Real.log M ≤ cA * Real.sqrt (Real.log y)) (χ : DirichletCharacter ℂ M) :
    ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      C * y * Real.exp (-c * Real.sqrt (Real.log y)) + 2 * y * Real.exp (-(Real.sqrt (Real.log y) / 2)) := by sorry

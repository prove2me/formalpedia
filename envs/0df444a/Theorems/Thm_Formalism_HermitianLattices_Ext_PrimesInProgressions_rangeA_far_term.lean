-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_rangeA_far_term
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.rangeA_far_term
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:18:14.106573+00:00
-- url     : https://prove2.me/theorems/b24931e5-de88-4705-92f9-1508b1760d1d
-- title:
--   Primes In Progressions: range A far term
-- statement:
--   The Primes In Progressions construction uses the range A far term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTRangeA.lean#L19-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTRangeA.lean#L19-L68

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.rangeA_far_term (M : ℕ) (hM : 8 ≤ M) (y cA β : ℝ) (hy : 2 ≤ y) (hcA : cA ≤ cZ)
    (hl : Real.log M ≤ cA * Real.sqrt (Real.log y)) (hβ : 1 / 2 ≤ β)
    (hr : ¬ InRegion cZ M (β : ℂ)) :
    ‖(y : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ 2 * y * Real.exp (-(Real.sqrt (Real.log y) / 2)) := by sorry

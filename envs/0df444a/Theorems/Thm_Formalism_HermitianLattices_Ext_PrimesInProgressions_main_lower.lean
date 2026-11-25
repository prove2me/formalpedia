-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_main_lower
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.main_lower
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:18:56.669798+00:00
-- url     : https://prove2.me/theorems/d83412ce-642d-4c9b-8dee-420d898be652
-- title:
--   Primes In Progressions: main lower
-- statement:
--   The Primes In Progressions construction uses the main lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiC.lean#L11-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiC.lean#L11-L51

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiC
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
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet ArithmeticFunction

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.main_lower {θ β η l X : ℝ} (hθ : |θ| ≤ 1) (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1) (hX : 16 ≤ X)
    (hl : l ≤ Real.log X) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hη : θ ≤ 0 ∨ η ≤ (1 - β) * l) :
    X * η / (2 * Real.log X) ≤ liX X - θ * liX (X ^ β) := by sorry

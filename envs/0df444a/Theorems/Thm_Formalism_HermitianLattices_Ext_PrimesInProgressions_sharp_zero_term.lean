-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_sharp_zero_term
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.sharp_zero_term
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:17:12.931568+00:00
-- url     : https://prove2.me/theorems/84dd7b6b-c580-5a80-918a-2c76479923fc
-- title:
--   Primes In Progressions: sharp zero term
-- statement:
--   The Primes In Progressions construction uses the sharp zero term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTSharp.lean#L13-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTSharp.lean#L13-L42

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTSharpA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTSharpB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTSharp
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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.sharp_zero_term {ρ : ℂ} (h1 : 1 / 2 ≤ ρ.re) (h2 : ρ.re < 1) {y δ : ℝ} (hy : 0 < y) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) :
    ‖((y * ((1 + δ) / δ) : ℝ) : ℂ) * ((((1 + δ) * y : ℝ) : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)) -
        (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))) - (y : ℂ) ^ ρ / ρ‖ ≤ 2 * δ * y * y ^ (ρ.re - 1) := by sorry

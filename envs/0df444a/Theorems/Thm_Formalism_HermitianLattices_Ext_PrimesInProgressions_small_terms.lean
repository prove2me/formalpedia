-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_small_terms
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.small_terms
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:18:23.642544+00:00
-- url     : https://prove2.me/theorems/d44f6e59-f7b0-441c-8173-d5e5a69e3007
-- title:
--   Primes In Progressions: small terms
-- statement:
--   The Primes In Progressions construction uses the small terms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiC.lean#L74-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiC.lean#L74-L112

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.small_terms {c₃ c₁ L l η φ : ℝ} (hc₃ : 0 ≤ c₃) (hc₁ : 0 < c₁) (hL : 16 * l ≤ L) (hL1 : 1 ≤ L)
    (hη : c₁ * Real.exp (-l) ≤ η) (hφ0 : 0 < φ) (hφ : φ ≤ Real.exp l) :
    44 * Real.exp (L / 2) * L ≤
      5632 * Real.exp (2 * c₃) / c₁ * Real.exp (-Real.sqrt (c₃ * L)) * (Real.exp L * η / (2 * L) / φ) := by sorry

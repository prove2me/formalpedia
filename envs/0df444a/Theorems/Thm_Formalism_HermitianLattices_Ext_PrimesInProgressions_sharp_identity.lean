-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_sharp_identity
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.sharp_identity
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:23.389806+00:00
-- url     : https://prove2.me/theorems/116da7a1-8880-4167-aecb-cf3b54ab12f8
-- title:
--   Primes In Progressions: sharp identity
-- statement:
--   The Primes In Progressions construction uses the sharp identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTSharpB.lean#L39-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTSharpB.lean#L39-L69

import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAP
import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTSharpB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex ArithmeticFunction
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.sharp_identity {N : ℕ} (χ : DirichletCharacter ℂ N) {y u : ℝ} (hy : 1 ≤ y) (hu : y < u) :
    ((y * u / (u - y) : ℝ) : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ u / (u : ℂ) - Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ)) - psiChi χ y =
      ∑ n ∈ Ioc ⌊y⌋₊ ⌊u⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod N) *
        ((y * u / (u - y) * (1 / n - 1 / u) : ℝ) : ℂ) := by sorry

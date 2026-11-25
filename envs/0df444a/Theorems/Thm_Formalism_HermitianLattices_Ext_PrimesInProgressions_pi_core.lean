-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_pi_core
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.pi_core
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:17:30.470659+00:00
-- url     : https://prove2.me/theorems/72ac946c-5f5b-5cec-9ac2-45985b67f4ca
-- title:
--   Primes In Progressions: pi core
-- statement:
--   The Primes In Progressions construction uses the pi core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiC.lean#L114-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTPiC.lean#L114-L212

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.pi_core (M : ℕ) [NeZero M] (h8 : 8 ∣ M) (b : ℕ) (hb : b.Coprime M)
    (e : Option (DirichletCharacter ℂ M × ℝ)) {θ β η c A c₁ X : ℝ}
    (hθ : |θ| ≤ 1) (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1)
    (hmain : ∀ t : ℝ, 0 ≤ t → ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * mainPsi e χ t =
      ((t - θ * t ^ β / β : ℝ) : ℂ))
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hη : θ ≤ 0 ∨ η ≤ (1 - β) * Real.log M) (hc₁ : 0 < c₁)
    (hηl : c₁ * (M : ℝ) ^ (-1 : ℝ) ≤ η) (hc : 0 < c) (hA : 0 ≤ A) (hX : 0 < X)
    (hL : 16 * Real.log M ≤ Real.log X)
    (hP : ∀ y : ℝ, √X ≤ y → y ≤ X → ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi e χ y‖ ≤
      A * y * η * (Real.exp (-(c * Real.log y / Real.log M)) + Real.exp (-(c * Real.sqrt (Real.log y))))) :
    |(piAP X M b : ℝ) - (liX X - θ * liX (X ^ β)) / (M.totient : ℝ)| ≤
      (10 * A + 5632 * Real.exp (2 * min (c / 2) (c ^ 2 / 2)) / c₁) *
        (Real.exp (-(min (c / 2) (c ^ 2 / 2) * Real.log X / Real.log M)) +
          Real.exp (-Real.sqrt (min (c / 2) (c ^ 2 / 2) * Real.log X))) *
        ((liX X - θ * liX (X ^ β)) / (M.totient : ℝ)) := by sorry

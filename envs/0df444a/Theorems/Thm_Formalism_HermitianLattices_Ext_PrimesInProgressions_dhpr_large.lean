-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhpr_large
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.dhpr_large
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:59:16.327576+00:00
-- url     : https://prove2.me/theorems/5227a2f2-c615-51aa-9c03-0449279b5c94
-- title:
--   Primes In Progressions: dhpr large
-- statement:
--   The Primes In Progressions construction uses the dhpr large property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHPrimeD.lean#L12-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHPrimeD.lean#L12-L67

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPrimeC
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPrimeD
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
open LSeries ArithmeticFunction DirichletCharacter

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.dhpr_large {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1) (k : ℕ)
    {σ η : ℝ} (hσ : 1 ≤ σ) (hση : σ - 1 = η) (hη : 0 < η) (hη1 : η ≤ 1) (v0 V : ℕ) (hV : v0 ≤ V)
    {A CH : ℝ} (hA : 0 ≤ A) (hCH : 0 ≤ CH)
    (hHyp : ∀ v : ℕ, ∑ n ∈ Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊,
        (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) ≤
          A + CH * M * (((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2)))) :
    ∑ n ∈ Ioc ⌊Real.exp (v0 : ℝ)⌋₊ ⌊Real.exp (V : ℝ)⌋₊, dhprF χ₁ k σ n ≤
      2 * A * (2 * Real.exp 2 * ((k : ℝ) + 2) * (((k : ℝ) + 1) * k.factorial) / η ^ (k + 2))
      + 2 * CH * M * (Real.exp 1 * (((k : ℝ) + 1) * k.factorial) / η ^ (k + 1) *
          (20 * Real.exp (-((v0 : ℝ) / 4)))) := by sorry

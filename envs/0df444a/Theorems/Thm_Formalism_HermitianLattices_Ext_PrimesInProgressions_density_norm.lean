-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_density_norm
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.density_norm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:15:28.635891+00:00
-- url     : https://prove2.me/theorems/17dd2a0d-06b4-56d0-a4a1-5782b4ccf560
-- title:
--   Primes In Progressions: density norm
-- statement:
--   The Primes In Progressions construction uses the density norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTZSumB.lean#L11-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTZSumB.lean#L11-L71

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DeuringHeilbronnM
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTZSumB
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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.density_norm (h : LogDensityM) :
    ∃ a B C : ℝ, 1 ≤ a ∧ 0 ≤ B ∧ 1 ≤ C ∧
      ∀ (M : ℕ) [NeZero M] (T v : ℝ) (S : Finset (DirichletCharacter ℂ M × ℂ)), 3 ≤ M → 2 ≤ T →
      (∀ p ∈ S, 1 / 2 ≤ p.2.re ∧ p.2.re ≤ 1 ∧ Real.log ((M : ℝ) * T) * (1 - p.2.re) ≤ v ∧ |p.2.im| ≤ T ∧
        IsLZero p.1 p.2) →
      (∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|) →
      (S.card : ℝ) ≤ C * Real.exp (a * v) * Real.log ((M : ℝ) * T) ^ B := by sorry

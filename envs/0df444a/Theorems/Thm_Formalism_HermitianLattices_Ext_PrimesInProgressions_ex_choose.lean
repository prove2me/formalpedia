-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_choose
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_choose
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:55:08.282386+00:00
-- url     : https://prove2.me/theorems/e7eca166-b2b3-4e36-aa83-9557ffe7ba5a
-- title:
--   Primes In Progressions: ex choose
-- statement:
--   The Primes In Progressions construction uses the ex choose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplPick.lean#L43-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplPick.lean#L43-L110

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplBox
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplPick
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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_choose : ∃ C : ℝ, 0 < C ∧ ∀ κ : ℝ, 0 < κ → κ ≤ 1 / 20 →
    ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (T : ℝ), 3 ≤ M → 2 ≤ T →
    ∃ σ₁ T' δ : ℝ, 1 - κ ≤ σ₁ ∧ σ₁ ≤ 1 - 3 * κ / 4 ∧ T ≤ T' ∧ T' ≤ T + 1 ∧ 0 < δ ∧ δ ≤ 1 / 20 ∧
      κ / (C * (T + 1) * Real.log ((M : ℝ) * (T + 2))) ≤ δ ∧
      (∀ ρ : ℂ, exLF χ ρ = 0 → 9 / 10 ≤ ρ.re → |ρ.im| ≤ T + 3 → δ ≤ |σ₁ - ρ.re|) ∧
      (∀ ρ : ℂ, exLF χ ρ = 0 → 9 / 10 ≤ ρ.re → δ ≤ |(|ρ.im| - T')|) := by sorry

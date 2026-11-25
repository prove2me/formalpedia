-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_core
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_core
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:16:01.674641+00:00
-- url     : https://prove2.me/theorems/2e6e8235-1448-4bc6-9578-db743697ac13
-- title:
--   Primes In Progressions: exm core
-- statement:
--   The Primes In Progressions construction uses the exm core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplMainB.lean#L31-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplMainB.lean#L31-L168

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplPick
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplNeg
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRectF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplEdge
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplMainA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplMainB
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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_core : ∃ C₂ C₃ : ℝ, 0 < C₂ ∧ 0 ≤ C₃ ∧ ∀ (κ : ℝ), 0 < κ → κ ≤ 1 / 20 →
    ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (T σ₁ T' δ : ℝ), 3 ≤ M → 2 ≤ T →
    1 - κ ≤ σ₁ → σ₁ ≤ 1 - 3 * κ / 4 → T ≤ T' → T' ≤ T + 1 → 0 < δ → δ ≤ 1 / 20 →
    (∀ ρ : ℂ, exLF χ ρ = 0 → 9 / 10 ≤ ρ.re → |ρ.im| ≤ T + 3 → δ ≤ |σ₁ - ρ.re|) →
    (∀ ρ : ℂ, exLF χ ρ = 0 → 9 / 10 ≤ ρ.re → δ ≤ |(|ρ.im| - T')|) →
    ∀ Z : Finset ℂ, (∀ ρ : ℂ, ρ ∈ Z ↔ (exLF χ ρ = 0 ∧ σ₁ < ρ.re ∧ |ρ.im| < T')) →
    ∀ y : ℝ, 2 ≤ y →
      ‖Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ) - explicitFormulaConstant χ - (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0) +
                ∑ ρ ∈ Z, (exOrd χ ρ : ℂ) * (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))‖ ≤
        1 / (2 * Real.pi * y) * (2 * (Real.log y + C₃) * (Real.exp 1 * y) / T' +
          2 * T' * (C₂ * (2 * Real.log ((M : ℝ) * T)) / δ + 4 / (3 * κ)) * y ^ σ₁ / (σ₁ * (1 - σ₁)) +
          (3 * (C₂ * (2 * Real.log ((M : ℝ) * T)) / δ + 1) * (Real.exp 1 * y) / T' ^ 2 +
           3 * (C₂ * (2 * Real.log ((M : ℝ) * T)) / δ + 1) * (Real.exp 1 * y) / T' ^ 2)) := by sorry

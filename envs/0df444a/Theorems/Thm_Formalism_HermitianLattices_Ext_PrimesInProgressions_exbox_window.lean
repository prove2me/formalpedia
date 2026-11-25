-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exbox_window
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.exbox_window
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:38:55.483418+00:00
-- url     : https://prove2.me/theorems/bdba27f9-327f-4140-a1bd-a1b8ca0933c6
-- title:
--   Primes In Progressions: exbox window
-- statement:
--   The Primes In Progressions construction uses the exbox window property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplBox.lean#L62-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplBox.lean#L62-L113

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLocL
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplBox
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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.exbox_window {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (hM : 3 ≤ M) {C0 : ℝ} (hC0 : 0 < C0)
    (D : ℝ → Finset ℂ)
    (hD : ∀ (u : ℝ) (ρ : ℂ), ρ ∈ D u ↔
      (ρ ∈ Metric.closedBall ((101 / 100 : ℂ) + u * I) (2 / 15) ∧ exLF χ ρ = 0))
    (hS : ∀ u : ℝ, ((∑ ρ ∈ D u, exOrd χ ρ : ℕ) : ℝ) ≤ C0 * Real.log ((M : ℝ) * (|u| + 2)))
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, exLF χ ρ = 0 ∧ 9 / 10 ≤ ρ.re) (t : ℝ) :
    ((∑ ρ ∈ Z.filter (fun ρ => |ρ.im - t| ≤ 1), exOrd χ ρ : ℕ) : ℝ) ≤
      30 * C0 * Real.log ((M : ℝ) * (|t| + 2)) := by sorry

-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exbox_mem_ball
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.exbox_mem_ball
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:38:51.615627+00:00
-- url     : https://prove2.me/theorems/4d0e8269-4bd8-42ef-ac7a-6a21c5bb9654
-- title:
--   Primes In Progressions: exbox mem ball
-- statement:
--   The Primes In Progressions construction uses the exbox mem ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplBox.lean#L48-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplBox.lean#L48-L60

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.exbox_mem_ball {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) {ρ : ℂ} {u : ℝ}
    (h0 : exLF χ ρ = 0) (h1 : 9 / 10 ≤ ρ.re) (h2 : |ρ.im - u| ≤ 1 / 14) :
    ρ ∈ Metric.closedBall ((101 / 100 : ℂ) + u * I) (2 / 15) := by sorry

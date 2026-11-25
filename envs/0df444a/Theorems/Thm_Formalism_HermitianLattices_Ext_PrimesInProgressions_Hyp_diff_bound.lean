-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_diff_bound
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.diff_bound
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:17:44.88814+00:00
-- url     : https://prove2.me/theorems/240ca746-c4bc-472d-afac-e4d143d0cc7a
-- title:
--   Hyp: diff bound
-- statement:
--   The Hyp construction uses the diff bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHHyper.lean#L45-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHHyper.lean#L45-L110

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DHFinish2Of
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperC
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyper
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
open Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.diff_bound (hχ : χ ≠ 1) (N₀ N₁ : ℕ) (h0 : 1 ≤ N₀) (h01 : N₀ ≤ N₁) :
    (cF χ N₁ - cF χ N₀).re ≤ ‖DirichletCharacter.LFunction χ 1‖ * (Real.log N₁ - Real.log N₀) +
      86 * ((q : ℝ) + 1) * ((Real.log N₀ + 1) / √(N₀ : ℝ)) := by sorry

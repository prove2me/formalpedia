-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_divSq_cube
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.divSq_cube
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:19:37.567824+00:00
-- url     : https://prove2.me/theorems/43c6add3-e99f-5678-a3b3-76ba2b6d2954
-- title:
--   Dens: div Sq cube
-- statement:
--   The Dens construction uses the div Sq cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensDiv.lean#L52-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensDiv.lean#L52-L100

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZMoll
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensDiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.divSq_cube (x : ℕ) :
    ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, ((Nat.lcm p.1 p.2 : ℕ) : ℝ)⁻¹ ≤ (∑ k ∈ Icc 1 x, ((k : ℝ))⁻¹) ^ 3 := by sorry

-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_space_side
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.space_side
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:29:53.744409+00:00
-- url     : https://prove2.me/theorems/7608e874-9a3e-5f34-be0e-5a157745b7f7
-- title:
--   Dens: space side
-- statement:
--   The Dens construction uses the space side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensSpace.lean#L27-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensSpace.lean#L27-L58

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSpace
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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.space_side (Q : Finset ℝ) (f : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T) (h1 : ∀ x ∈ Q, 1 ≤ f x)
    (h2 : ∀ x ∈ Q, f x ≤ 2 * T) (hsp : ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → 1 ≤ |f x - f y|) :
    ∑ x ∈ Q, 1 / f x ≤ 1 + Real.log (2 * T + 1) := by sorry

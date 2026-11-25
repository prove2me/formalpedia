-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Dens_off_diagonal_bound
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.off_diagonal_bound
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:41:48.8468+00:00
-- url     : https://prove2.me/theorems/1dc8a1ca-a88a-4f7a-b1ea-fbcb87d557e7
-- title:
--   Dens: off diagonal bound
-- statement:
--   The Dens construction uses the off diagonal bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensBlock.lean#L108-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDensBlock.lean#L108-L156

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensDiv
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensPair
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSpace
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDual
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensBlock
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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.off_diagonal_bound : Offdiag := by sorry

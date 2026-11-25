-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_rpow_sigma
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_rpow_sigma
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:13:56.215986+00:00
-- url     : https://prove2.me/theorems/b78d483a-171d-521f-9aa7-8b7853031dae
-- title:
--   Primes In Progressions: exm rpow sigma
-- statement:
--   The Primes In Progressions construction uses the exm rpow sigma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplMainB.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplMainB.lean#L25-L29

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_rpow_sigma (y : ℝ) (hy : 2 ≤ y) : y ^ (1 + 1 / Real.log y) = Real.exp 1 * y := by sorry

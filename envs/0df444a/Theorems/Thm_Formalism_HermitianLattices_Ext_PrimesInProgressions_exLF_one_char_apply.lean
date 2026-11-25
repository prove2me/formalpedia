-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_one_char_apply
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.exLF_one_char_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:13:46.492375+00:00
-- url     : https://prove2.me/theorems/7e44bbb7-3271-4a22-8e04-0b04b262e58f
-- title:
--   Primes In Progressions: ex LF one char apply
-- statement:
--   The Primes In Progressions construction uses the ex LF one char apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplLF.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplLF.lean#L19-L21

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLF
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
variable {M : ℕ} [NeZero M]

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.exLF_one_char_apply {s : ℂ} (hs : s ≠ 1) :
    exLF (1 : DirichletCharacter ℂ M) s = (s - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) s := by sorry

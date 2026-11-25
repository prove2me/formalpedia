-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_of_ne
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.exLF_of_ne
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:11:00.153958+00:00
-- url     : https://prove2.me/theorems/89092d36-3deb-4260-9dd3-a510674d2de4
-- title:
--   Primes In Progressions: ex LF of ne
-- statement:
--   The Primes In Progressions construction uses the ex LF of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplLF.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplLF.lean#L13-L14

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.exLF_of_ne {χ : DirichletCharacter ℂ M} (h : χ ≠ 1) : exLF χ = DirichletCharacter.LFunction χ := by sorry

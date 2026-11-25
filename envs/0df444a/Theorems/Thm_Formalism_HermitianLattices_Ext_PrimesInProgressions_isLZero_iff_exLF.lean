-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_isLZero_iff_exLF
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.isLZero_iff_exLF
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:09:46.897853+00:00
-- url     : https://prove2.me/theorems/19209dc8-3524-580b-97ec-557819ce7a8a
-- title:
--   Primes In Progressions: is LZero iff ex LF
-- statement:
--   The Primes In Progressions construction uses the is LZero iff ex LF property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplLF.lean#L40-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplLF.lean#L40-L49

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.isLZero_iff_exLF (χ : DirichletCharacter ℂ M) (s : ℂ) : IsLZero χ s ↔ exLF χ s = 0 := by sorry

-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exOrd_pos
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.exOrd_pos
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:10:15.369142+00:00
-- url     : https://prove2.me/theorems/5a638e58-5cad-4079-b0b4-77c1b720a1e1
-- title:
--   Primes In Progressions: ex Ord pos
-- statement:
--   The Primes In Progressions construction uses the ex Ord pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplLF.lean#L92-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplLF.lean#L92-L98

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.exOrd_pos (χ : DirichletCharacter ℂ M) {ρ : ℂ} (hρ : exLF χ ρ = 0) : 1 ≤ exOrd χ ρ := by sorry

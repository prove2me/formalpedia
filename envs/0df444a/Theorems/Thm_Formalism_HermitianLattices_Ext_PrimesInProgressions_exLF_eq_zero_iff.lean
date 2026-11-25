-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_eq_zero_iff
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.exLF_eq_zero_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:13:08.263424+00:00
-- url     : https://prove2.me/theorems/846e48d3-fb99-4374-8686-43c6d4537891
-- title:
--   Primes In Progressions: ex LF eq zero iff
-- statement:
--   The Primes In Progressions construction uses the ex LF eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplLF.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplLF.lean#L33-L38

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.exLF_eq_zero_iff (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : s ≠ 1) :
    exLF χ s = 0 ↔ DirichletCharacter.LFunction χ s = 0 := by sorry

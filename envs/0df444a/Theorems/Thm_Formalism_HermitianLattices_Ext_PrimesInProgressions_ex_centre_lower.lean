-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ex_centre_lower
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_centre_lower
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:28:26.774799+00:00
-- url     : https://prove2.me/theorems/9053cc48-be24-4948-b562-a2d1b0c80d71
-- title:
--   Primes In Progressions: ex centre lower
-- statement:
--   The Primes In Progressions construction uses the ex centre lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplLocL.lean#L28-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplLocL.lean#L28-L43

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLoc
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLocL
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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.ex_centre_lower {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (t : ℝ) :
    1 / 10100 ≤ ‖exLF χ ((101 / 100 : ℂ) + t * I)‖ := by sorry

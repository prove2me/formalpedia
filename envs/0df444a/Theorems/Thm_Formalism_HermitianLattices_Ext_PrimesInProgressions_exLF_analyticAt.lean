-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_analyticAt
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.exLF_analyticAt
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:12:07.916257+00:00
-- url     : https://prove2.me/theorems/5c0f7b5e-2370-4557-8066-05479713b9b4
-- title:
--   Primes In Progressions: ex LF analytic At
-- statement:
--   The Primes In Progressions construction uses the ex LF analytic At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplLF.lean#L84-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplLF.lean#L84-L85

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.exLF_analyticAt (χ : DirichletCharacter ℂ M) (z : ℂ) : AnalyticAt ℂ (exLF χ) z := by sorry

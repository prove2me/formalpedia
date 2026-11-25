-- Prove2me | Theorems.Thm_Formalism_L2_Col_lambdaAtPrime_eq_one_of_no_residueCharacter
-- name    : Formalism.L2.Col.lambdaAtPrime_eq_one_of_no_residueCharacter
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:45:09.473467+00:00
-- url     : https://prove2.me/theorems/191278cc-5d03-4832-a19c-ff58c57b6cd6
-- title:
--   Col: lambda At Prime eq one of no residue Character
-- statement:
--   The Col construction uses the lambda At Prime eq one of no residue Character property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L995-L1003
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L995-L1003

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

theorem Formalism.L2.Col.lambdaAtPrime_eq_one_of_no_residueCharacter (ξ : Formalism.L2.DIV.Chr F E L) (P : HeightOneSpectrum (𝓞 E)) (n a b : ℕ)
    (hno : ¬ ∃ χ, Formalism.L2.DIV.IsResChar ξ P χ) : lamQP ξ P n a b = 1 := by sorry

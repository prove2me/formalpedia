-- Prove2me | Theorems.Thm_Formalism_L2_Col_atW_restrictScalars
-- name    : Formalism.L2.Col.atW_restrictScalars
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:08.511983+00:00
-- url     : https://prove2.me/theorems/e25da4f7-e8fb-46b7-8086-ee324e5aa0b7
-- title:
--   Col: at W restrict Scalars
-- statement:
--   The Col construction uses the at W restrict Scalars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L134-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L134-L138

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.L2.Col.atW_restrictScalars (w : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) V) :
    (atW w L).restrictScalars (𝓞 K) = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L := by sorry

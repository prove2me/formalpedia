-- Prove2me | Theorems.Thm_Formalism_L2_Col_length_ow_quot_prW
-- name    : Formalism.L2.Col.length_ow_quot_prW
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:12.573835+00:00
-- url     : https://prove2.me/theorems/332b6606-ff74-405d-9900-528f909c9c90
-- title:
--   Col: length ow quot pr W
-- statement:
--   The Col construction uses the length ow quot pr W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L326-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L326-L328

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

theorem Formalism.L2.Col.length_ow_quot_prW (w : HeightOneSpectrum (𝓞 K)) :
    Module.length (Ow w) (Ow w ⧸ Ideal.span {((prW w : ℕ) : Ow w)}) = eW w := by sorry

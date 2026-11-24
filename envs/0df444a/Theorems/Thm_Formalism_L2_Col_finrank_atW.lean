-- Prove2me | Theorems.Thm_Formalism_L2_Col_finrank_atW
-- name    : Formalism.L2.Col.finrank_atW
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:38.364227+00:00
-- url     : https://prove2.me/theorems/5a08c718-40e3-4077-adb3-3f7f511c4951
-- title:
--   Col: finrank at W
-- statement:
--   The Col construction uses the finrank at W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L356-L373
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L356-L373

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

theorem Formalism.L2.Col.finrank_atW (w : HeightOneSpectrum (𝓞 K)) {L : Submodule (𝓞 K) V} (h : L.FG) :
    Module.finrank (Ow w) (atW w L) = Module.finrank K (Submodule.span K (L : Set V)) := by sorry

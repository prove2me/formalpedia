-- Prove2me | Theorems.Thm_Formalism_L2_Col_absIrrChar_finite
-- name    : Formalism.L2.Col.absIrrChar_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:59.680876+00:00
-- url     : https://prove2.me/theorems/d2673b7b-488b-4921-804a-04a026b51cc6
-- title:
--   Col: abs Irr Char finite
-- statement:
--   The Col construction uses the abs Irr Char finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GoodXgFin.lean#L81-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GoodXgFin.lean#L81-L90

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Columns_GoodXgFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.L2.DIV
variable {G : Type} [Group G] [Fintype G]

theorem Formalism.L2.Col.absIrrChar_finite {K : Type} [Field K] [CharZero K] : {χ : G → K | IsAbsIrrChar χ}.Finite := by sorry

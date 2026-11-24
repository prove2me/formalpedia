-- Prove2me | Theorems.Thm_Formalism_L2_Col_gxIrrSet_finite
-- name    : Formalism.L2.Col.gxIrrSet_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:57.02613+00:00
-- url     : https://prove2.me/theorems/1fabdeaf-d483-4b83-a61b-083522bc3ae1
-- title:
--   Col: gx Irr Set finite
-- statement:
--   The Col construction uses the gx Irr Set finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GoodXgFin.lean#L79-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GoodXgFin.lean#L79-L79

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

theorem Formalism.L2.Col.gxIrrSet_finite {k : Type} [Field k] [IsAlgClosed k] [CharZero k] : (gxIrrSet (G := G) k).Finite := by sorry

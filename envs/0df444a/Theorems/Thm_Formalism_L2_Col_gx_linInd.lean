-- Prove2me | Theorems.Thm_Formalism_L2_Col_gx_linInd
-- name    : Formalism.L2.Col.gx_linInd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:12.910087+00:00
-- url     : https://prove2.me/theorems/07adf83b-1e6e-4345-b95d-9a37af929125
-- title:
--   Col: gx lin Ind
-- statement:
--   The Col construction uses the gx lin Ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GoodXgFin.lean#L48-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GoodXgFin.lean#L48-L77

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

theorem Formalism.L2.Col.gx_linInd {k : Type} [Field k] [IsAlgClosed k] [CharZero k] :
    LinearIndependent k (fun ψ : gxIrrSet (G := G) k => (ψ : G → k)) := by sorry

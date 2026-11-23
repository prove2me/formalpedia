-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_mem_intDel_iff
-- name    : Formalism.L2.Col.GSD.mem_intDel_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:40:37.841285+00:00
-- url     : https://prove2.me/theorems/fcca15af-9b63-4c1e-880c-81faa45eae83
-- title:
--   GSD: mem int Del iff
-- statement:
--   The GSD construction uses the mem int Del iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L59-L61

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.DivisionValues Formalism.L2.DIV
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Col.GSD
variable (S : GSD K)

theorem Formalism.L2.Col.GSD.mem_intDel_iff (h : S.Ok) (s : S.Sec) (φ : S.EqFun) :
    φ ∈ S.intDel ↔ ∀ c, (φ : S.D → S.V) (s.rep c) ∈ S.Del (s.rep c) := by sorry

-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_resFree_apply
-- name    : Formalism.L2.Col.GSD.resFree_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:21.694805+00:00
-- url     : https://prove2.me/theorems/63587bc4-873a-47ae-ace2-d8ce9dcbcbd7
-- title:
--   GSD: res Free apply
-- statement:
--   The GSD construction uses the res Free apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L224-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L224-L225

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

theorem Formalism.L2.Col.GSD.resFree_apply (h : S.Ok) (s : S.Sec) (hf : S.Free) (φ : S.EqFun) (c : S.Cl) :
    S.resFree h s hf φ c = (φ : S.D → S.V) (s.rep c) := by sorry

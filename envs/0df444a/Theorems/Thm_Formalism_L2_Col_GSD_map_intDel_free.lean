-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_map_intDel_free
-- name    : Formalism.L2.Col.GSD.map_intDel_free
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:43.53824+00:00
-- url     : https://prove2.me/theorems/bcf66c2c-ce56-4750-95f5-248f157b6363
-- title:
--   GSD: map int Del free
-- statement:
--   The GSD construction uses the map int Del free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L253-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L253-L269

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

theorem Formalism.L2.Col.GSD.map_intDel_free (h : S.Ok) (s : S.Sec) (hf : S.Free) :
    S.intDel.map ((S.resFree h s hf : S.EqFun →ₗ[K] (S.Cl → S.V)).restrictScalars (𝓞 K)) =
      Submodule.pi Set.univ fun c => S.Del (s.rep c) := by sorry

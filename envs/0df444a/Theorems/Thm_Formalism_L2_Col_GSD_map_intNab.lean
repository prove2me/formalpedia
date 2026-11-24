-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_map_intNab
-- name    : Formalism.L2.Col.GSD.map_intNab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:56.876656+00:00
-- url     : https://prove2.me/theorems/32fb32ee-50d4-4fa2-a3a6-998c897a5808
-- title:
--   GSD: map int Nab
-- statement:
--   The GSD construction uses the map int Nab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L85-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L85-L97

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

theorem Formalism.L2.Col.GSD.map_intNab (h : S.Ok) (s : S.Sec) :
    S.intNab.map ((S.coordOf h s : S.EqFun →ₗ[K] (Fin (S.toCSDOf h s).dim → K)).restrictScalars (𝓞 K)) =
      (S.toCSDOf h s).nabLat := by sorry

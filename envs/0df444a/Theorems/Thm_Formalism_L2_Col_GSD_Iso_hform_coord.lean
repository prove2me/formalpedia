-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_Iso_hform_coord
-- name    : Formalism.L2.Col.GSD.Iso.hform_coord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:24.078961+00:00
-- url     : https://prove2.me/theorems/e446db12-bfdb-4f4f-adc3-9116fd674817
-- title:
--   Iso: hform coord
-- statement:
--   The Iso construction uses the hform coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L380-L386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L380-L386

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
open Formalism.L2.Col.GSD Formalism.L2.Col.GSD.Iso
variable {S S' : GSD K} (e : GSD.Iso S S')

theorem Formalism.L2.Col.GSD.Iso.hform_coord (h : S.Ok) (h' : S'.Ok) (s : S.Sec) (s' : S'.Sec) (x y : Fin (S.toCSDOf h s).dim → K) :
    hform (S'.toCSDOf h' s').H (e.coord h h' s s' x) (e.coord h h' s s' y) = hform (S.toCSDOf h s).H x y := by sorry

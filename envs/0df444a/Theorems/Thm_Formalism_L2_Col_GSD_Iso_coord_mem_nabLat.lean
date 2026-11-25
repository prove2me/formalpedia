-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_Iso_coord_mem_nabLat
-- name    : Formalism.L2.Col.GSD.Iso.coord_mem_nabLat
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:44:17.694374+00:00
-- url     : https://prove2.me/theorems/b6ead75f-fb5a-4f8c-88a0-0bc30991b773
-- title:
--   Iso: coord mem nab Lat
-- statement:
--   The Iso construction uses the coord mem nab Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L388-L391
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L388-L391

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

theorem Formalism.L2.Col.GSD.Iso.coord_mem_nabLat (h : S.Ok) (h' : S'.Ok) (s : S.Sec) (s' : S'.Sec) (x : Fin (S.toCSDOf h s).dim → K) :
    e.coord h h' s s' x ∈ (S'.toCSDOf h' s').nabLat ↔ x ∈ (S.toCSDOf h s).nabLat := by sorry

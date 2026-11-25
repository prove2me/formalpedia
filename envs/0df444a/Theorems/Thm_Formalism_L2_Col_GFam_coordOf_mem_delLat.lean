-- Prove2me | Theorems.Thm_Formalism_L2_Col_GFam_coordOf_mem_delLat
-- name    : Formalism.L2.Col.GFam.coordOf_mem_delLat
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:46:00.440256+00:00
-- url     : https://prove2.me/theorems/d986941b-d23a-5459-921f-bdabbaa234b3
-- title:
--   GFam: coord Of mem del Lat
-- statement:
--   The GFam construction uses the coord Of mem del Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1131-L1136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1131-L1136

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
open Formalism.L2.Col.GFam
variable (F : GFam K)

theorem Formalism.L2.Col.GFam.coordOf_mem_delLat (h : F.Ok) (s : ∀ b, (F.mem b).Sec) (φ : F.Forms) :
    F.coordOf h s φ ∈ (F.toCSDOf h s).delLat ↔ φ ∈ F.intDel := by sorry

-- Prove2me | Theorems.Thm_Formalism_L2_Col_GFam_ipOf_coord
-- name    : Formalism.L2.Col.GFam.ipOf_coord
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:55:10.961151+00:00
-- url     : https://prove2.me/theorems/0f3ed2ed-0d3a-50cb-90ef-b86bb79c4252
-- title:
--   GFam: ip Of coord
-- statement:
--   The GFam construction uses the ip Of coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1138-L1145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1138-L1145

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

theorem Formalism.L2.Col.GFam.ipOf_coord (h : F.Ok) (s : ∀ b, (F.mem b).Sec) (φ ψ : F.Forms) :
    F.ipOf h s φ ψ = hform (F.toCSDOf h s).H (F.coordOf h s φ) (F.coordOf h s ψ) := by sorry

-- Prove2me | Theorems.Thm_Formalism_L2_Col_GFam_I_coordOf
-- name    : Formalism.L2.Col.GFam.I_coordOf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:45:49.999328+00:00
-- url     : https://prove2.me/theorems/6d787113-5c95-454c-9790-ed2fb0053788
-- title:
--   GFam: I coord Of
-- statement:
--   The GFam construction uses the I coord Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1118-L1122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1118-L1122

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

theorem Formalism.L2.Col.GFam.I_coordOf (h : F.Ok) (s : ∀ b, (F.mem b).Sec) (φ : F.Forms) :
    (F.toCSDOf h s).I (F.coordOf h s φ) = (F.resOf h s φ).1 := by sorry

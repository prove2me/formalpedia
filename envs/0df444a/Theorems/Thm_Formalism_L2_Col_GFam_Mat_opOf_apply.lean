-- Prove2me | Theorems.Thm_Formalism_L2_Col_GFam_Mat_opOf_apply
-- name    : Formalism.L2.Col.GFam.Mat.opOf_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:16.526101+00:00
-- url     : https://prove2.me/theorems/72d6c1e1-cec6-4411-a54c-eb8423cd3750
-- title:
--   Mat: op Of apply
-- statement:
--   The Mat construction uses the op Of apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1173-L1175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1173-L1175

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

theorem Formalism.L2.Col.GFam.Mat.opOf_apply {F F' : GFam K} (M : Mat F F') (h : F.Ok) (s : ∀ b, (F.mem b).Sec) (φ : F.Forms)
    (b' : F'.β) : M.opOf h s φ b' = ∑ b, (M b b').opOf (h b) (s b) (φ b) := by sorry

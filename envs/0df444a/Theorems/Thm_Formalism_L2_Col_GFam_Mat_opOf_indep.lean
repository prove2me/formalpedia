-- Prove2me | Theorems.Thm_Formalism_L2_Col_GFam_Mat_opOf_indep
-- name    : Formalism.L2.Col.GFam.Mat.opOf_indep
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:52:05.983117+00:00
-- url     : https://prove2.me/theorems/988a2761-5cec-47d8-8584-abc261597d31
-- title:
--   Mat: op Of indep
-- statement:
--   The Mat construction uses the op Of indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1177-L1181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1177-L1181

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

theorem Formalism.L2.Col.GFam.Mat.opOf_indep {F F' : GFam K} (M : Mat F F') (h : F.Ok) (s s' : ∀ b, (F.mem b).Sec) :
    M.opOf h s = M.opOf h s' := by sorry

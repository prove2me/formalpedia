-- Prove2me | Theorems.Thm_Formalism_L2_Col_GFam_toCSDOf_rat
-- name    : Formalism.L2.Col.GFam.toCSDOf_rat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:07:39.457402+00:00
-- url     : https://prove2.me/theorems/ea814015-5fab-49ab-bd91-72c174cec91d
-- title:
--   GFam: to CSDOf rat
-- statement:
--   The GFam construction uses the to CSDOf rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1167-L1171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1167-L1171

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_toCSDOf_rat

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

theorem Formalism.L2.Col.GFam.toCSDOf_rat [Nonempty F.β] (h : F.Ok) (R : ∀ b, (F.mem b).Rat) (s : ∀ b, (F.mem b).Sec) :
    (F.toCSDOf h s).Rat := by sorry

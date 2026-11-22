-- Prove2me | Theorems.Thm_Formalism_L2_Col_GFam_toCSDOf_good
-- name    : Formalism.L2.Col.GFam.toCSDOf_good
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:07:51.610318+00:00
-- url     : https://prove2.me/theorems/ba11fef7-8002-4712-ac06-1798fe81f232
-- title:
--   GFam: to CSDOf good
-- statement:
--   The GFam construction uses the to CSDOf good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1155-L1165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1155-L1165

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_toCSDOf_good

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

theorem Formalism.L2.Col.GFam.toCSDOf_good {n : ℕ} [Nonempty F.β] (G : F.Good n) (s : ∀ b, (F.mem b).Sec) :
    (F.toCSDOf (fun b => (G b).ok) s).Good n := by sorry

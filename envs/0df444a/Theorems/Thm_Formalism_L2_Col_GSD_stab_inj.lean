-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_stab_inj
-- name    : Formalism.L2.Col.GSD.stab_inj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:09:11.13432+00:00
-- url     : https://prove2.me/theorems/d0277058-63a7-41a6-b0e0-66ecbd8f364e
-- title:
--   GSD: stab inj
-- statement:
--   The GSD construction uses the stab inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1394-L1407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1394-L1407

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
variable (K)

theorem Formalism.L2.Col.GSD.stab_inj {Γ H D : Type} [Group Γ] [Group H] [MulAction (Γ × H) D]
    (free : ∀ (h : H) (d : D), ((1, h) : Γ × H) • d = d → h = 1) (d : D) :
    Function.Injective (fun x : MulAction.stabilizer (Γ × H) d => (x : Γ × H).1) := by sorry

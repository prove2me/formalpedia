-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_Iso_ipOf_onForms
-- name    : Formalism.L2.Col.GSD.Iso.ipOf_onForms
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:09:11.321884+00:00
-- url     : https://prove2.me/theorems/3b21fbad-87aa-4845-9acc-03c2801d9262
-- title:
--   Iso: ip Of on Forms
-- statement:
--   The Iso construction uses the ip Of on Forms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L359-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L359-L368

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

theorem Formalism.L2.Col.GSD.Iso.ipOf_onForms (h : S.Ok) (h' : S'.Ok) (s : S.Sec) (s' : S'.Sec) (φ ψ : S.EqFun) :
    S'.ipOf h' s' (e.onForms φ) (e.onForms ψ) = S.ipOf h s φ ψ := by sorry

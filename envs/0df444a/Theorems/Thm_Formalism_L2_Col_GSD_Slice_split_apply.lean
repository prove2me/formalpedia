-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_Slice_split_apply
-- name    : Formalism.L2.Col.GSD.Slice.split_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:43:26.436492+00:00
-- url     : https://prove2.me/theorems/7f89228b-eeb3-4159-b536-850837f33f79
-- title:
--   Slice: split apply
-- statement:
--   The Slice construction uses the split apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L808-L809
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L808-L809

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
variable (S : GSD K)
variable (A : Type) [Group A] [MulAction A S.D]
open Formalism.L2.Col.GSD.Slice
variable {S A} (σ : S.Slice A)
variable [SMulCommClass A S.G S.D]

theorem Formalism.L2.Col.GSD.Slice.split_apply (φ : S.EqFun) (b : A) (t : σ.T) :
    ((σ.split φ b : (S.restr σ.T).EqFun) : σ.T → S.V) t = (φ : S.D → S.V) (b • (t : S.D)) := by sorry

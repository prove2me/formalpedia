-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_Slice_ipOf_split
-- name    : Formalism.L2.Col.GSD.Slice.ipOf_split
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:44:32.359239+00:00
-- url     : https://prove2.me/theorems/be017922-2076-433d-aa7d-020cfc6ebe82
-- title:
--   Slice: ip Of split
-- statement:
--   The Slice construction uses the ip Of split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L889-L900
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L889-L900

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

theorem Formalism.L2.Col.GSD.Slice.ipOf_split [Fintype A] (h : S.Ok) (s : S.Sec) (sT : (S.restr σ.T).Sec) (φ ψ : S.EqFun) :
    S.ipOf h s φ ψ = ∑ b : A, (S.restr σ.T).ipOf (S.restr_ok h σ.T) sT (σ.split φ b) (σ.split ψ b) := by sorry

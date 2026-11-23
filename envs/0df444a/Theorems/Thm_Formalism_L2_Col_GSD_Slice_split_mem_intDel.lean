-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_Slice_split_mem_intDel
-- name    : Formalism.L2.Col.GSD.Slice.split_mem_intDel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:22.637052+00:00
-- url     : https://prove2.me/theorems/0404a56a-4e4f-4a72-898d-d49ba312e34b
-- title:
--   Slice: split mem int Del
-- statement:
--   The Slice construction uses the split mem int Del property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L843-L845
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L843-L845

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

theorem Formalism.L2.Col.GSD.Slice.split_mem_intDel (hN : ∀ (b : A) (d : S.D), S.Del (b • d) = S.Del d) (φ : S.EqFun) :
    φ ∈ S.intDel ↔ ∀ b, σ.split φ b ∈ (S.restr σ.T).intDel := by sorry

-- Prove2me | Theorems.Thm_Formalism_L2_Col_LocOp_op_mem_intOf
-- name    : Formalism.L2.Col.LocOp.op_mem_intOf
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:52:34.549559+00:00
-- url     : https://prove2.me/theorems/291b6a5f-2965-564b-9910-7b22fc31a9b9
-- title:
--   Loc Op: op mem int Of
-- statement:
--   The Loc Op construction uses the op mem int Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L999-L1004
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L999-L1004

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

theorem Formalism.L2.Col.LocOp.op_mem_intOf {S S' : GSD K} (A : LocOp S S') (N : S.D → Submodule (𝓞 K) S.V)
    (N' : S'.D → Submodule (𝓞 K) S'.V) (hk : ∀ d' d, ∀ x ∈ N d, A.ker d' d x ∈ N' d') (φ : S.EqFun)
    (hφ : φ ∈ S.intOf N) : A.op φ ∈ S'.intOf N' := by sorry

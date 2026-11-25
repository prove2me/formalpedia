-- Prove2me | Theorems.Thm_Formalism_L2_Col_ClsKer_opOf_mem_intOf_DGam
-- name    : Formalism.L2.Col.ClsKer.opOf_mem_intOf_DGam
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:49:03.099198+00:00
-- url     : https://prove2.me/theorems/25ee29db-f41d-5740-9564-5db0650dff1b
-- title:
--   Cls Ker: op Of mem int Of DGam
-- statement:
--   The Cls Ker construction uses the op Of mem int Of DGam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1022-L1027
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1022-L1027

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

theorem Formalism.L2.Col.ClsKer.opOf_mem_intOf_DGam {S S' : GSD K} (A : ClsKer S S') (h : S.Ok) (s : S.Sec)
    (N : S.D → Submodule (𝓞 K) S.V) (N' : S'.D → Submodule (𝓞 K) S'.V)
    (hk : ∀ d d', ∀ x ∈ N d, A.k d d' x ∈ N' d') (φ : S.EqFun) (hφ : φ ∈ S.intOf N) :
    ((S.toCSDOf h s).DGam : 𝓞 K) • A.opOf h s φ ∈ S'.intOf N' := by sorry

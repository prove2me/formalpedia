-- Prove2me | Theorems.Thm_Formalism_L2_Col_ClsKer_opOf_mem_intOf
-- name    : Formalism.L2.Col.ClsKer.opOf_mem_intOf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:43.328378+00:00
-- url     : https://prove2.me/theorems/ed00fd00-b72d-4206-b0b0-63951bf246d8
-- title:
--   Cls Ker: op Of mem int Of
-- statement:
--   The Cls Ker construction uses the op Of mem int Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1006-L1020
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1006-L1020

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

theorem Formalism.L2.Col.ClsKer.opOf_mem_intOf {S S' : GSD K} (A : ClsKer S S') (h : S.Ok) (s : S.Sec)
    (N : S.D → Submodule (𝓞 K) S.V) (N' : S'.D → Submodule (𝓞 K) S'.V)
    (hk : ∀ d d', ∀ x ∈ N d, A.k d d' x ∈ N' d') (n : ℕ) (hn : ∀ c, (S.toCSDOf h s).wt c ∣ n) (φ : S.EqFun)
    (hφ : φ ∈ S.intOf N) : (n : 𝓞 K) • A.opOf h s φ ∈ S'.intOf N' := by sorry

-- Prove2me | Theorems.Thm_Formalism_L2_Col_BiPair_sumOf_mem
-- name    : Formalism.L2.Col.BiPair.sumOf_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:43:55.188588+00:00
-- url     : https://prove2.me/theorems/2ceccc31-0fd3-46df-8908-c0f56ce0139f
-- title:
--   Bi Pair: sum Of mem
-- statement:
--   The Bi Pair construction uses the sum Of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1078-L1083
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1078-L1083

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
open Formalism.L2.Col.BiPair
variable {S S' : GSD K} (P : BiPair S S')

theorem Formalism.L2.Col.BiPair.sumOf_mem (h' : S'.Ok) (s' : S'.Sec) (N : S.D → Submodule (𝓞 K) S.V) (N' : S'.D → Submodule (𝓞 K) S'.V)
    (hB : ∀ d', ∀ x ∈ N (P.p d'), ∀ y ∈ N' d', P.B x y ∈ (1 : Submodule (𝓞 K) K)) (n : ℕ)
    (hn : ∀ c, (S'.toCSDOf h' s').wt c ∣ n) (φ : S.EqFun) (hφ : φ ∈ S.intOf N) (ψ : S'.EqFun)
    (hψ : ψ ∈ S'.intOf N') : (n : 𝓞 K) • P.sumOf h' s' φ ψ ∈ (1 : Submodule (𝓞 K) K) := by sorry

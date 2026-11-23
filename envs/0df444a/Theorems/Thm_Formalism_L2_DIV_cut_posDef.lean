-- Prove2me | Theorems.Thm_Formalism_L2_DIV_cut_posDef
-- name    : Formalism.L2.DIV.cut_posDef
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:45:44.297605+00:00
-- url     : https://prove2.me/theorems/2436c427-082a-4902-8681-37bc9a18fc37
-- title:
--   DIV: cut pos Def
-- statement:
--   The DIV construction uses the cut pos Def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L1036-L1057
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/ProjLemmas.lean#L1036-L1057

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
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
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues

theorem Formalism.L2.DIV.cut_posDef {K : Type} [Field K] [NumberField K] [StarRing K] {n d : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (E : Matrix (Fin n) (Fin d) K)
    (hE : Function.Injective E.mulVec) (hrat : ∀ i j, E i j ∈ cmMax K) (N : ℕ) (hN : 0 < N)
    (v : InfinitePlace K) (hpos : (H.map v.embedding).PosDef) :
    (((N : K)⁻¹ • (Eᴴ * H * E)).map v.embedding).PosDef := by sorry

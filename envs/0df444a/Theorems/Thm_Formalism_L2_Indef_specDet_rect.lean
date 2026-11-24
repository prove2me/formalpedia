-- Prove2me | Theorems.Thm_Formalism_L2_Indef_specDet_rect
-- name    : Formalism.L2.Indef.specDet_rect
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:48.105543+00:00
-- url     : https://prove2.me/theorems/ff9f9fd4-418b-48dc-9876-7f96bb546143
-- title:
--   Indef: spec Det rect
-- statement:
--   The Indef construction uses the spec Det rect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L174-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L174-L194

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
import Definitions.Def_Formalism_DivisorInequality_StatementObj
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.L2.Indef.specDet_rect (hS : SpecDet) (v : InfinitePlace K) {D dQ : ℕ}
    (XQ : InfinitePlace K → Matrix (Fin dQ) (Fin dQ) ℂ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ)
    (hXQ : ∀ u, IsUnit (XQ u).det) (hXE : ∀ u, IsUnit (XE u).det)
    (ι : Matrix (Fin D) (Fin dQ) K) (hι : Function.Bijective ι.mulVec)
    (J : Type) [Fintype J] (dZ dW : J → ℕ)
    (XT : ∀ j, InfinitePlace K → Matrix (Fin (dZ j)) (Fin (dZ j)) ℂ)
    (XW : ∀ j, InfinitePlace K → Matrix (Fin (dW j)) (Fin (dW j)) ℂ)
    (hXT : ∀ j u, IsUnit (XT j u).det) (hXW : ∀ j u, IsUnit (XW j u).det)
    (θ : ∀ j, Matrix (Fin (dW j)) (Fin (dZ j)) K) (hθ : ∀ j, Function.Bijective (θ j).mulVec)
    (Ix : Type) [Fintype Ix] (Qp : Ix → Submodule K (Fin dQ → K))
    (Tq : ∀ j, Ix → Submodule K (Fin (dZ j) → K))
    (h1 : iSupIndep Qp) (h2 : (⨆ p, Qp p) = ⊤) (h3 : ∀ j, iSupIndep (Tq j)) (h4 : ∀ j, (⨆ p, Tq j p) = ⊤)
    (h5 : ∀ j p, finrank K (Qp p) = finrank K (Tq j p)) (s : ℝ) (lam : J → Ix → ℝ)
    (h6 : ∀ p, IsScalarOn XQ XE v ι (Qp p) (s * ∏ j, lam j p))
    (h7 : ∀ j p, IsScalarOn (XT j) (XW j) v (θ j) (Tq j p) (lam j p)) :
    detRatio XQ XE ι v = s ^ D * ∏ j, detRatio (XT j) (XW j) (θ j) v := by sorry

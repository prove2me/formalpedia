-- Prove2me | Theorems.Thm_Formalism_L2_Indef_IndefCols_height
-- name    : Formalism.L2.Indef.IndefCols.height
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:47:46.958564+00:00
-- url     : https://prove2.me/theorems/a87fb18f-93ea-4310-ac22-18dee9e04544
-- title:
--   Indef Cols: height
-- statement:
--   The Indef Cols construction uses the height property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L341-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L341-L389

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

theorem Formalism.L2.Indef.IndefCols.height (hH : HeightBoundConstant) {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc}
    {N : IndefNum Bs} [Nonempty Bs.Ix] (wf : Df.WF) (S : IndefCols Df Dc Sp N) (u : Dc.Mem) (hXc : ∀ v, IsUnit (Dc.Xc u v).det)
    (hne : S.col.B u ≠ 0)
    (X0 : InfinitePlace K → Matrix (Fin (Df.nV Bs.μ0)) (Fin (Df.nV Bs.μ0)) ℂ)
    (hX0 : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = (Df.HV Bs.μ0).map v.embedding)
    (pU : InfinitePlace K → ℝ)
    (hpU : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u)
      (Pi.basisFun K (Fin (Df.nV Bs.μ0))).dualBasis (Formalism.HN.dualFrame X0) v (Dc.Pt u Bs.μ0) ≤ pU v) :
    Formalism.HN.htMap (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) (Pi.basisFun K (Fin S.D)).dualBasis
              (Formalism.HN.dualFrame S.XE) (S.col.B u) ≤
      (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (pU v ^ 2) - ∑ j, N.l6 j - meanLog S.κ := by sorry

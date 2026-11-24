-- Prove2me | Theorems.Thm_Formalism_L2_Indef_IndefColsR_height
-- name    : Formalism.L2.Indef.IndefColsR.height
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:42.495617+00:00
-- url     : https://prove2.me/theorems/0e0548ab-984d-43e8-8a38-569d19579a12
-- title:
--   Indef Cols R: height
-- statement:
--   The Indef Cols R construction uses the height property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/PairingConditionOfInverseMatrixIdentity.lean#L344-L391
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/PairingConditionOfInverseMatrixIdentity.lean#L344-L391

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity
import Theorems.Thm_Formalism_L2_Indef_IndefCols_height

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
open Formalism.L2.Indef.IndefColsR
variable {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs}
  (S : IndefColsR Df Dc Sp N)

theorem Formalism.L2.Indef.IndefColsR.height (hH : HeightBoundConstant) [Nonempty Bs.Ix] (wf : Df.WF) (u : Dc.Mem) (hXc : ∀ v, IsUnit (Dc.Xc u v).det)
    (hne : S.col.B u ≠ 0)
    (X0 : InfinitePlace K → Matrix (Fin (Df.nV Bs.μ0)) (Fin (Df.nV Bs.μ0)) ℂ)
    (hX0 : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = (Df.HV Bs.μ0).map v.embedding)
    (pU : InfinitePlace K → ℝ)
    (hpU : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u)
      (Pi.basisFun K (Fin (Df.nV Bs.μ0))).dualBasis (Formalism.HN.dualFrame X0) v (Dc.Pt u Bs.μ0) ≤ pU v) :
    Formalism.HN.htMap (Pi.basisFun K (Fin (Dc.a u))) (Dc.Xc u) (Pi.basisFun K (Fin S.D)).dualBasis
              (Formalism.HN.dualFrame S.XE) (S.col.B u) ≤
      (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (pU v ^ 2) - ∑ j, N.l6 j - meanLog S.κ := by sorry

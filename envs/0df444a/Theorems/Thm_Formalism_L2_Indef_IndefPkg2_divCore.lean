-- Prove2me | Theorems.Thm_Formalism_L2_Indef_IndefPkg2_divCore
-- name    : Formalism.L2.Indef.IndefPkg2.divCore
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:23.000496+00:00
-- url     : https://prove2.me/theorems/dd19cf76-9192-4c6b-998b-cbb70cce19f8
-- title:
--   Indef Pkg2: div Core
-- statement:
--   The Indef Pkg2 construction uses the div Core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/PairingConditionOfInverseMatrixIdentity.lean#L168-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/PairingConditionOfInverseMatrixIdentity.lean#L168-L199

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity
import Theorems.Thm_Formalism_L2_Indef_IndefCore_divCore

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
open Formalism.L2.Indef.IndefPkg2
variable {Bs : DefBase K} {A : DefAmb Bs} {fc : DefSub A → DefFace Bs} {cf : ConvFace Bs} {C CH : ℝ}
  (P : IndefPkg2 A fc cf C CH)

theorem Formalism.L2.Indef.IndefPkg2.divCore [IsTotallyComplex K] (hM : Formalism.DivisorInequality.BoundsMu) (hS : SpecDet) (hR0 : GramDeterminantQuotientMetric)
    (hG : LatticeGlue) (hRam : RamBasic) (hH : HeightBoundConstant) [Nonempty Bs.Ix] (wf0 : (fc P.Zs).Df0.WF)
    (wf1 : (fc P.Zs).Df1.WF)
    (hde : 0 ≤ ((fc P.Zs).Z.num C CH).de) (hde3 : ((fc P.Zs).Z.num C CH).de ≤ 1 / 3)
    (eb : ∀ t, HeightOneSpectrum (𝓞 K) → Fin ((fc P.Zs).Df0.dQ t) → Fin ((fc P.Zs).Df0.dQ t) → K)
    (heb : ∀ t w, IsLocBasis ((fc P.Zs).Df0.abelian₂ t) w (eb t w))
    (Sy : Finset (HeightOneSpectrum (𝓞 K))) (hSy : P.core.base.Tw ⊆ Sy)
    (hG0 : ∀ y, y ∉ Sy → vw y ((fc P.Zs).Df0.Gm eb (P.core.base.μ y) y) = 0)
    (LG E3 : ℝ) (E2 : Bs.J → ℝ) (gy : HeightOneSpectrum (𝓞 K) → ℝ) (ηy : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ)
    (hi : ∀ y ∈ Sy, (vw y ((fc P.Zs).Df0.Gm eb (P.core.base.μ y) y) : ℝ) ≤ (P.core.base.D : ℝ) * gy y)
    (hLG : ∑ y ∈ Sy, lw y * gy y ≤ LG)
    (hiv : ∀ y ∈ P.core.base.Tw, ∀ j, (jw ((fc P.Zs).Df0.HT j (P.core.base.μ y)) y ((fc P.Zs).Df0.Tl j (P.core.base.μ y)) : ℝ) ≤
      ((ramw y : ℝ) * ((fc P.Zs).Z.num C CH).J0 (P.core.base.μ y) y j) * (P.core.base.D : ℝ) + ηy y j)
    (hE2 : ∀ j, ∑ y ∈ P.core.base.Tw, lw y * ηy y j / (P.core.base.D : ℝ) ≤ E2 j)
    (hE3 : ∑ y ∈ Sy, lw y * (2 / ellw y ^ 2) ≤ E3)
    (u : (fc P.Zs).Dc.Mem) (hXc : ∀ v, IsUnit (((fc P.Zs).Dc.Xc u v).det)) (hne : P.core.cols.col.B u ≠ 0)
    (X0 : InfinitePlace K → Matrix (Fin ((fc P.Zs).Df1.nV Bs.μ0)) (Fin ((fc P.Zs).Df1.nV Bs.μ0)) ℂ)
    (hX0 : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = ((fc P.Zs).Df1.HV Bs.μ0).map v.embedding)
    (pU : InfinitePlace K → ℝ)
    (hpU : ∀ v, Formalism.HN.opNormAt (Pi.basisFun K (Fin ((fc P.Zs).Dc.a u))) ((fc P.Zs).Dc.Xc u)
      (Pi.basisFun K (Fin ((fc P.Zs).Df1.nV Bs.μ0))).dualBasis (Formalism.HN.dualFrame X0) v ((fc P.Zs).Dc.Pt u Bs.μ0) ≤ pU v)
    (X : ℝ)
    (hX : X = (∑ j, ((fc P.Zs).Z.num C CH).l3 j) +
      2 * (∑ j, ∑ y ∈ P.core.base.Tw, lw y * ((ramw y : ℝ) * ((fc P.Zs).Z.num C CH).F0 y j)) + LG +
      (∑ j, (((fc P.Zs).Z.num C CH).E1 j + E2 j)) + E3) :
    P.core.cols.muCC + Formalism.HN.htMap (Pi.basisFun K (Fin ((fc P.Zs).Dc.a u))) ((fc P.Zs).Dc.Xc u)
        (Pi.basisFun K (Fin P.core.cols.D)).dualBasis (Formalism.HN.dualFrame P.core.cols.XE) (P.core.cols.col.B u) ≤
      X + 3 * ((fc P.Zs).Z.num C CH).de * (X + ((fc P.Zs).Z.num C CH).hh + 28 * ((fc P.Zs).Z.num C CH).la) +
        28 * ((fc P.Zs).Z.num C CH).la +
        ((1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (pU v ^ 2) - ∑ j, ((fc P.Zs).Z.num C CH).l6 j) := by sorry

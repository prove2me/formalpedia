-- Prove2me | Theorems.Thm_Formalism_L2_Indef_IndefSide_boundsMu
-- name    : Formalism.L2.Indef.IndefSide.boundsMu
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:18:45.212911+00:00
-- url     : https://prove2.me/theorems/4b1402de-6f23-4222-b20a-2cee0c28536f
-- title:
--   Indef Side: bounds Mu
-- statement:
--   The Indef Side construction uses the bounds Mu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L271-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L271-L334

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

theorem Formalism.L2.Indef.IndefSide.boundsMu [IsTotallyComplex K] (hM : Formalism.DivisorInequality.BoundsMu) (hS : SpecDet) (hR0 : GramDeterminantQuotientMetric)
    (hG : LatticeGlue) (hRam : RamBasic) {Bs : DefBase K} {Df : DefSide Bs} {N : IndefNum Bs} (wf : Df.WF)
    (S : IndefSide Df N) (hU : S.toIndefData.Untwisted N)
    (eb : ∀ t, HeightOneSpectrum (𝓞 K) → Fin (Df.dQ t) → Fin (Df.dQ t) → K)
    (heb : ∀ t w, IsLocBasis (Df.abelian₂ t) w (eb t w))
    (Sy : Finset (HeightOneSpectrum (𝓞 K))) (hSy : S.Tw ⊆ Sy)
    (hG0 : ∀ y, y ∉ Sy → vw y (Df.Gm eb (S.μ y) y) = 0)
    (LG E3 : ℝ) (E2 : Bs.J → ℝ) (gy : HeightOneSpectrum (𝓞 K) → ℝ) (ηy : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ)
    (hi : ∀ y ∈ Sy, (vw y (Df.Gm eb (S.μ y) y) : ℝ) ≤ (S.D : ℝ) * gy y)
    (hLG : ∑ y ∈ Sy, lw y * gy y ≤ LG)
    (hiv : ∀ y ∈ S.Tw, ∀ j, (jw (Df.HT j (S.μ y)) y (Df.Tl j (S.μ y)) : ℝ) ≤
      ((ramw y : ℝ) * N.J0 (S.μ y) y j) * (S.D : ℝ) + ηy y j)
    (hE2 : ∀ j, ∑ y ∈ S.Tw, lw y * ηy y j / (S.D : ℝ) ≤ E2 j)
    (hE3 : ∑ y ∈ Sy, lw y * (2 / ellw y ^ 2) ≤ E3) :
    Formalism.HN.muDef (Pi.basisFun K (Fin S.D)).dualBasis (Formalism.HN.dualFrame S.XE) (Formalism.HN.dualLat S.RR) ≤
      meanLog S.κ + (∑ j, N.l3 j) + 2 * (∑ j, ∑ y ∈ S.Tw, lw y * ((ramw y : ℝ) * N.F0 y j)) + LG +
        (∑ j, (N.E1 j + E2 j)) + E3 := by sorry

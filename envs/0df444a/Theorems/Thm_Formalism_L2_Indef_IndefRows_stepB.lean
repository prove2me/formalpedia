-- Prove2me | Theorems.Thm_Formalism_L2_Indef_IndefRows_stepB
-- name    : Formalism.L2.Indef.IndefRows.stepB
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:59:29.06009+00:00
-- url     : https://prove2.me/theorems/e34043cf-4e86-4f29-81ea-3a7a5b18b408
-- title:
--   Indef Rows: step B
-- statement:
--   The Indef Rows construction uses the step B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L236-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefUse.lean#L236-L269

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

theorem Formalism.L2.Indef.IndefRows.stepB [IsTotallyComplex K] (hB : StepBW) (hS : SpecDet) (hR0 : GramDeterminantQuotientMetric) (hRb : LemmaRb)
    (hG : LatticeGlue) {Bs : DefBase K} {Df : DefSide Bs} (wf : Df.WF) (S : IndefRows Df)
    (eb : ∀ t, HeightOneSpectrum (𝓞 K) → Fin (Df.dQ t) → Fin (Df.dQ t) → K)
    (heb : ∀ t w, IsLocBasis (Df.abelian₂ t) w (eb t w)) :
    (Function.support fun w => lw w * ((vw w (Df.Gm eb (S.μ w) w) : ℝ) + ∑ j, S.Aw j w)).Finite ∧
    lcv S.XE S.RR ≤ (S.D : ℝ) * meanLog S.κ + ∑ j, lcv (S.XW j) (S.M j) +
      ∑ᶠ w, lw w * ((vw w (Df.Gm eb (S.μ w) w) : ℝ) + ∑ j, S.Aw j w) := by sorry

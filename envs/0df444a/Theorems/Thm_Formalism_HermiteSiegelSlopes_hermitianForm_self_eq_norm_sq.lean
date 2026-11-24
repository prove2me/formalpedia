-- Prove2me | Theorems.Thm_Formalism_HermiteSiegelSlopes_hermitianForm_self_eq_norm_sq
-- name    : Formalism.HermiteSiegelSlopes.hermitianForm_self_eq_norm_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:43.195716+00:00
-- url     : https://prove2.me/theorems/771daec2-fad8-4e0e-9842-cf86b4553dd0
-- title:
--   Hermite Siegel Slopes: hermitian Form self eq norm sq
-- statement:
--   The Hermite Siegel Slopes construction uses the hermitian Form self eq norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L256-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L256-L262

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset
noncomputable section
open Formalism Formalism.HermiteSiegelSlopes
open Formalism.HN
open scoped nonZeroDivisors
open IsDedekindDomain
variable {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Fintype ι] [DecidableEq ι]
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem Formalism.HermiteSiegelSlopes.hermitianForm_self_eq_norm_sq (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x : V) : Formalism.HermitianLatticesTheory.majAt b X v x x = ((Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 : ℝ) : ℂ) := by sorry

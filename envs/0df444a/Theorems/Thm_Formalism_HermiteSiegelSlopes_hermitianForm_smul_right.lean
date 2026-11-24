-- Prove2me | Theorems.Thm_Formalism_HermiteSiegelSlopes_hermitianForm_smul_right
-- name    : Formalism.HermiteSiegelSlopes.hermitianForm_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:26.761205+00:00
-- url     : https://prove2.me/theorems/b00c1d9e-3de0-4488-9668-267c12499a8b
-- title:
--   Hermite Siegel Slopes: hermitian Form smul right
-- statement:
--   The Hermite Siegel Slopes construction uses the hermitian Form smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L224-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L224-L238

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

theorem Formalism.HermiteSiegelSlopes.hermitianForm_smul_right (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (a : K) (x y : V) : Formalism.HermitianLatticesTheory.majAt b X v x (a • y) =
      v.embedding a * Formalism.HermitianLatticesTheory.majAt b X v x y := by sorry

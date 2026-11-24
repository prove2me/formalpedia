-- Prove2me | Theorems.Thm_Formalism_HermiteSiegelSlopes_hermitianForm_add_right
-- name    : Formalism.HermiteSiegelSlopes.hermitianForm_add_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:30:22.910776+00:00
-- url     : https://prove2.me/theorems/25b026e5-f82d-424b-9ac2-7453b00ff102
-- title:
--   Hermite Siegel Slopes: hermitian Form add right
-- statement:
--   The Hermite Siegel Slopes construction uses the hermitian Form add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L210-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L210-L222

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

theorem Formalism.HermiteSiegelSlopes.hermitianForm_add_right (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x y z : V) : Formalism.HermitianLatticesTheory.majAt b X v x (y + z) =
      Formalism.HermitianLatticesTheory.majAt b X v x y + Formalism.HermitianLatticesTheory.majAt b X v x z := by sorry

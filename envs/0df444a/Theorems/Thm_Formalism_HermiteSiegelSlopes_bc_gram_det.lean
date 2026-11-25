-- Prove2me | Theorems.Thm_Formalism_HermiteSiegelSlopes_bc_gram_det
-- name    : Formalism.HermiteSiegelSlopes.bc_gram_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:53.826406+00:00
-- url     : https://prove2.me/theorems/64e27076-67d1-482a-97ac-b0d609bf4413
-- title:
--   Hermite Siegel Slopes: bc gram det
-- statement:
--   The Hermite Siegel Slopes construction uses the bc gram det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L277-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L277-L330

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
variable [StarRing F] [StarRing E]

theorem Formalism.HermiteSiegelSlopes.bc_gram_det [IsTotallyComplex F]
    (XF : InfinitePlace F → Matrix ι ι ℂ) (XE : InfinitePlace E → Matrix ι ι ℂ)
    (hn : ∀ (w : InfinitePlace E) (x : ι → F),
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun E ι) XE w (fun i => algebraMap F E (x i)) =
        Formalism.HermitianLatticesTheory.normAt (Pi.basisFun F ι) XF (w.comap (algebraMap F E)) x)
    (w : InfinitePlace E) {j : ℕ} (e : Fin j → ι → F) :
    (gramPl (Pi.basisFun E ι) XE w (fun a => bcMap (E := E) (e a))).det =
      (gramPl (Pi.basisFun F ι) XF (w.comap (algebraMap F E)) e).det := by sorry

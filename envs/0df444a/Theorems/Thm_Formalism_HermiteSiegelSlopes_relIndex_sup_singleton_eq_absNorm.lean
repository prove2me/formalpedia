-- Prove2me | Theorems.Thm_Formalism_HermiteSiegelSlopes_relIndex_sup_singleton_eq_absNorm
-- name    : Formalism.HermiteSiegelSlopes.relIndex_sup_singleton_eq_absNorm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:30:30.440795+00:00
-- url     : https://prove2.me/theorems/ff47dc43-48ec-49da-83f4-9d2da2d3a55e
-- title:
--   Hermite Siegel Slopes: rel Index sup singleton eq abs Norm
-- statement:
--   The Hermite Siegel Slopes construction uses the rel Index sup singleton eq abs Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L338-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean#L338-L349

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
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]

theorem Formalism.HermiteSiegelSlopes.relIndex_sup_singleton_eq_absNorm (A : Submodule (𝓞 K) V) (m : V) :
    A.toAddSubgroup.relIndex (A ⊔ Submodule.span (𝓞 K) {m}).toAddSubgroup =
      Ideal.absNorm (A.comap (LinearMap.toSpanSingleton (𝓞 K) V m) : Ideal (𝓞 K)) := by sorry

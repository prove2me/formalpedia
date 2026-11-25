-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_gq_mem
-- name    : Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.gq_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:21:20.680863+00:00
-- url     : https://prove2.me/theorems/fa872093-41db-5413-8de8-46ec72cfe81b
-- title:
--   Limit Normal Forms: gq mem
-- statement:
--   The Limit Normal Forms construction uses the gq mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/HatProd.lean#L92-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/HatProd.lean#L92-L95

import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_OpLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_HatProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
set_option linter.unusedSectionVars false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
open Formalism.FourierDecayAlt.P.CutMP
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
variable {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}

theorem Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.gq_mem (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (q : MA.Qp P.r P.TT) :
    B.gq Bs q.1 ∈ B.GV P.k P.r ∩ Gauge.OmB Bs := by sorry

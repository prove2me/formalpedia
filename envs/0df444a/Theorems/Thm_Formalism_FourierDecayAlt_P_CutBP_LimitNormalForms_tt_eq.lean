-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_tt_eq
-- name    : Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.tt_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:14:52.66758+00:00
-- url     : https://prove2.me/theorems/da12fe73-879f-5a52-ac71-af97d93d187f
-- title:
--   Limit Normal Forms: tt eq
-- statement:
--   The Limit Normal Forms construction uses the tt eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/HatProd.lean#L89-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/HatProd.lean#L89-L90

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

theorem Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.tt_eq (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') : P.TT = Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' := by sorry

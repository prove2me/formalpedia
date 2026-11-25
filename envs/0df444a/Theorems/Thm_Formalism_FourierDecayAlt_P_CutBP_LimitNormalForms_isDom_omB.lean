-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_isDom_omB
-- name    : Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.isDom_omB
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:32:22.985329+00:00
-- url     : https://prove2.me/theorems/b4cce9d9-b520-54e2-82b2-199b73becb57
-- title:
--   Limit Normal Forms: is Dom om B
-- statement:
--   The Limit Normal Forms construction uses the is Dom om B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/HatProd.lean#L72-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/HatProd.lean#L72-L85

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

theorem Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.isDom_omB {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) : Q.IsDom k r Bs.z Bs.z' 0 (Gauge.OmB Bs) := by sorry

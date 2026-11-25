-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_commutes_loc
-- name    : Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.commutes_loc
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:19:22.384207+00:00
-- url     : https://prove2.me/theorems/220cae2f-33a4-5e45-9282-ed16b2435e75
-- title:
--   Limit Normal Forms: commutes loc
-- statement:
--   The Limit Normal Forms construction uses the commutes loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/OpLocal.lean#L145-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/OpLocal.lean#L145-L157

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatOpA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UsCompose
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_OpLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ContDiff Topology
set_option linter.unusedSectionVars false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.commutes_loc (D : RealPlaceData k r Wp Wq) {UU : Set (Mat k r)} {Θ : DiffOp k r Wp Wq} (hC : Commutes D UU Θ)
    {p : SS k r} (hp : D.inSS p) {VV : Set (Mat k r)} {J : Mat k r → (Wq →L[ℂ] Wp)}
    (hJ : CkOn (opOrder Θ : ℕ∞) VV J) {g : Mat k r} (hg : g ∈ UU) (hgG : g ∈ GV k r) (hgV : sgs p g ∈ VV) :
    opApply Θ (rho D p J) g = rho D p (opApply Θ J) g := by sorry

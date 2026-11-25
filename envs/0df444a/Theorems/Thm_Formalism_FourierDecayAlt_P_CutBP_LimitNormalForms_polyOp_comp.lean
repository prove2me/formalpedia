-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_polyOp_comp
-- name    : Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.polyOp_comp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:36:33.648879+00:00
-- url     : https://prove2.me/theorems/f1ad224e-d1c3-4407-b29f-b7d071078e9c
-- title:
--   Limit Normal Forms: poly Op comp
-- statement:
--   The Limit Normal Forms construction uses the poly Op comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/OpLocal.lean#L347-L386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/OpLocal.lean#L347-L386

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

theorem Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.polyOp_comp [FiniteDimensional ℂ Wp] {o₁ κ₁ o₂ κ₂ : ℕ} {Θ₁ Θ₂ : DiffOp k r Wp Wq}
    (h₁ : CutMP.PolyOp o₁ κ₁ Θ₁) (h₂ : CutMP.PolyOp o₂ κ₂ Θ₂) :
    ∃ Θ : DiffOp k r Wp Wq, CutMP.PolyOp (o₁ + o₂) (κ₁ + κ₂) Θ ∧
      (∀ (VV : Set (Mat k r)) (F : Mat k r → (Wq →L[ℂ] Wp)), CkOn ((o₁ + o₂ : ℕ) : ℕ∞) VV F →
        ∀ g ∈ VV, g ∈ GV k r → opApply Θ F g = opApply Θ₁ (opApply Θ₂ F) g) ∧
      ∀ (D : RealPlaceData k r Wp Wq) (O : Set (Mat k r)), IsOpen O →
        Commutes D (GV k r ∩ O) Θ₁ → Commutes D (GV k r ∩ O) Θ₂ → Commutes D (GV k r ∩ O) Θ := by sorry

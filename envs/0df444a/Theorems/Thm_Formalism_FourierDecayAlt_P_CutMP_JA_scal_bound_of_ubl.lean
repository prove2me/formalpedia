-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_scal_bound_of_ubl
-- name    : Formalism.FourierDecayAlt.P.CutMP.JA.scal_bound_of_ubl
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:17:58.978746+00:00
-- url     : https://prove2.me/theorems/763416b4-7fc3-4a24-b1df-b4c695576e9f
-- title:
--   JA: scal bound of ubl
-- statement:
--   The JA construction uses the scal bound of ubl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJABddScalBound.lean#L26-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJABddScalBound.lean#L26-L57

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddScal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatPolyOK
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddScalBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA
noncomputable section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem Formalism.FourierDecayAlt.P.CutMP.JA.scal_bound_of_ubl (D : B.RealPlaceData k r Wp Wq) (φ : B.Mat k r → ℂ) (e γ : ℕ) (Bg : ℝ)
    (hBg : (e : ℝ) + γ ≤ Bg) (ε : ℝ)
    (h0 : ∃ C0 : ℝ, ∀ g ∈ regE D ε, ‖φ g‖ ≤ C0) (hU : ∀ n : ℕ, UBL φ (regE D ε) n e γ) (m : ℕ) :
    ∃ C : ℝ, ∀ u w : List (B.Mat k r),
      (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) → u.length + w.length ≤ m →
      ∀ g ∈ B.GV k r, ε ≤ Gf k r D.z D.z' g → ‖B.dLR u w φ g‖ ≤ C * B.gN g ^ (Bg * m) := by sorry

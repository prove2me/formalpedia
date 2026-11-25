-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_uwG_letter_poly
-- name    : Formalism.FourierDecayAlt.P.PBG.uwG_letter_poly
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:41:50.990443+00:00
-- url     : https://prove2.me/theorems/bf6b41e6-3e3e-5131-890f-cfd615707884
-- title:
--   PBG: uw G letter poly
-- statement:
--   The PBG construction uses the uw G letter poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean#L550-L556
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean#L550-L556

import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Classical
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r)

theorem Formalism.FourierDecayAlt.P.PBG.uwG_letter_poly {F : B.Mat k r → E} (hF : B.CkOn ⊤ (B.GV k r) F) (w : List C.Letter)
    (e' : Wd.Ix (Fin w.length)) (g₀ : B.Mat k r) (hg₀ : g₀ ∈ GV k r) (hD : Dmin k r z z' g₀ ⟨j, by omega⟩ ≠ 0)
    (b : Bool) (e : Fin 2) :
    ∃ c : Fin (j + 1) → E, c (Fin.last j) = (if e = 0 then D.uwG k r z z' F j hj w e' g₀ else 0) ∧
      ∀ Y : ℝ, D.vLet k r z z' j hj (b, Y) e (D.uwG k r z z' F j hj w e') g₀ =
        ∑ l : Fin (j + 1), ((Y : ℂ) ^ (l : ℕ)) • c l := by sorry

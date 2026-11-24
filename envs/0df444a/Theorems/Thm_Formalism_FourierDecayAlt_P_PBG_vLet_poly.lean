-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_vLet_poly
-- name    : Formalism.FourierDecayAlt.P.PBG.vLet_poly
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:19:01.21727+00:00
-- url     : https://prove2.me/theorems/89b1bf25-13de-45c0-89c2-6108f650a1ca
-- title:
--   PBG: v Let poly
-- statement:
--   The PBG construction uses the v Let poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean#L340-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGLet.lean#L340-L396

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

theorem Formalism.FourierDecayAlt.P.PBG.vLet_poly {j : ℕ} (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (G : B.Mat k r → E) (g₀ : B.Mat k r)
    (hg₀ : g₀ ∈ GV k r) (hD : Dmin k r z z' g₀ ⟨j, by omega⟩ ≠ 0) (hG : Loc (⊤ : ℕ∞) G g₀) (b : Bool) (e : Fin 2) :
    ∃ c : Fin (j + 1) → E, c (Fin.last j) = (if e = 0 then G g₀ else 0) ∧
      ∀ Y : ℝ, D.vLet k r z z' j hj (b, Y) e G g₀ = ∑ l : Fin (j + 1), ((Y : ℂ) ^ (l : ℕ)) • c l := by sorry

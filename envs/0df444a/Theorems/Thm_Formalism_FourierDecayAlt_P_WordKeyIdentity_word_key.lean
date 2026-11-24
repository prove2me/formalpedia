-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WordKeyIdentity_word_key
-- name    : Formalism.FourierDecayAlt.P.WordKeyIdentity.word_key
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:36:55.468929+00:00
-- url     : https://prove2.me/theorems/fc02db18-d754-4e6e-a063-7da7e00ff358
-- title:
--   Word Key Identity: word key
-- statement:
--   The Word Key Identity construction uses the word key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordKeyIdentity.lean#L46-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WordKeyIdentity.lean#L46-L61

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordKeyIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordKeyIdentity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.WordKeyIdentity.word_key (hW : JWords) (hR : RwRho) (D : RealPlaceData k r Wp Wq) {A : ℝ} {m : ℕ}
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hT : TransportedAlt k r A m) (hF : InCC A m F) {g : Mat k r} (hg : g ∈ Om k r D.z D.z')
    (w : List (Mat k r)) (hw : ∀ X ∈ w, unitLie k r X) (hl : w.length ≤ m) :
    Integrable (fun p => xiP D p • Rw w (rho D p F) g) D.μSS ∧
      Rw w (JF D F) g = ∫ p, xiP D p • Rw w (rho D p F) g ∂D.μSS := by sorry

-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_qminor_trn
-- name    : Formalism.FourierDecayAlt.P.JFxB.qminor_trn
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:09:09.807012+00:00
-- url     : https://prove2.me/theorems/d3b93a88-60db-4266-9150-e9103cd0b68e
-- title:
--   JFx B: qminor trn
-- statement:
--   The JFx B construction uses the qminor trn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CvRhoOfParts.lean#L130-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CvRhoOfParts.lean#L130-L159

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxB
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem Formalism.FourierDecayAlt.P.JFxB.qminor_trn (L : E →L[ℂ] E') {a b : Mat k r} (ha : a ∈ GV k r) (hb : b ∈ GV k r)
    (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E') → (Mat k r → E'))
    (Eop' : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
    (hI : ∀ c d (f : Mat k r → E), CkOn ((1 : ℕ) : ℕ∞) (GV k r) f →
      ∀ g ∈ GV k r, Eop c d (trn L a b f) g = trn L a b (Eop' c d f) g)
    (hC : ∀ c d (f f₂ : Mat k r → E'), (∀ g ∈ GV k r, f g = f₂ g) → ∀ g ∈ GV k r, Eop c d f g = Eop c d f₂ g)
    (hS' : ∀ c d (m : ℕ) (f : Mat k r → E), CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f →
      CkOn (m : ℕ∞) (GV k r) (Eop' c d f))
    {t : ℕ} (p q : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (f : Mat k r → E)
    (hf : CkOn ((t : ℕ) : ℕ∞) (GV k r) f) :
    ∀ g ∈ GV k r, qminorOp Eop p q u (trn L a b f) g = trn L a b (qminorOp Eop' p q u f) g := by sorry

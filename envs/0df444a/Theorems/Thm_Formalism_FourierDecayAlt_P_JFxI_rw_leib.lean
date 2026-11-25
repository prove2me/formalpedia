-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxI_rw_leib
-- name    : Formalism.FourierDecayAlt.P.JFxI.rw_leib
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:35:19.097796+00:00
-- url     : https://prove2.me/theorems/ea2dd6b6-cecb-48dd-9738-beb6ef0f57ad
-- title:
--   JFx I: rw leib
-- statement:
--   The JFx I construction uses the rw leib property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdjointLeibnizExpansion.lean#L167-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdjointLeibnizExpansion.lean#L167-L208

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfExhaustOfAvgCutoff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointLeibnizExpansion
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxI
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.JFxI.rw_leib (z z' : Fin (2 * r + k + 1) → ℂ) (A : Mat k r → (E →L[ℂ] E)) (f : Mat k r → E) (N : ℕ)
    (hA : CkOn ⊤ (Om k r z z') A) (hf : CkOn (N : ℕ∞) (Om k r z z') f) :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → w.length ≤ N → ∀ x ∈ Om k r z z',
      Rw w (fun y => A y (f y)) x = ((splits w).map fun uv => Rw uv.1 A x (Rw uv.2 f x)).sum := by sorry

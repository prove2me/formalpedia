-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FrameEntries_poly_contDiff
-- name    : Formalism.FourierDecayAlt.P.FrameEntries.poly_contDiff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:33:40.470031+00:00
-- url     : https://prove2.me/theorems/cc93d8ea-a44e-4d7f-b031-7d1c027220ed
-- title:
--   Frame Entries: poly cont Diff
-- statement:
--   The Frame Entries construction uses the poly cont Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameEntries.lean#L292-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameEntries.lean#L292-L312

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.FrameEntries
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.FrameEntries.poly_contDiff
    (p : MvPolynomial ((Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) ℂ) :
    ContDiff ℝ ∞ fun g : Mx k r => MvPolynomial.eval
      (Sum.elim (fun x => g x.1 x.2) (fun x => (Hpk k r * gᴴ * Hpk k r) x.1 x.2)) p := by sorry

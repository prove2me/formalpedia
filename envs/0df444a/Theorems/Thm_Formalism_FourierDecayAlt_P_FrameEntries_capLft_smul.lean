-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FrameEntries_capLft_smul
-- name    : Formalism.FourierDecayAlt.P.FrameEntries.capLft_smul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:41:21.44728+00:00
-- url     : https://prove2.me/theorems/33ad83af-0ac0-425e-97eb-04d08cded448
-- title:
--   Frame Entries: cap Lft smul
-- statement:
--   The Frame Entries construction uses the cap Lft smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameEntries.lean#L53-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameEntries.lean#L53-L66

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
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.FrameEntries.capLft_smul {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (w c : ℂ) (f : Mx k r → E) :
    capLft k r Bs w (fun x => c • f x) = fun x => c • capLft k r Bs w f x := by sorry

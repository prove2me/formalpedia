-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FrameEntries_foldl_smul
-- name    : Formalism.FourierDecayAlt.P.FrameEntries.foldl_smul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:34:03.418397+00:00
-- url     : https://prove2.me/theorems/17fa1583-5b41-42c5-a709-1e7aa43875e0
-- title:
--   Frame Entries: foldl smul
-- statement:
--   The Frame Entries construction uses the foldl smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameEntries.lean#L43-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameEntries.lean#L43-L51

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

theorem Formalism.FourierDecayAlt.P.FrameEntries.foldl_smul (L : List ((Mx k r → E) → Mx k r → E)) (c : ℂ)
    (hL : ∀ T ∈ L, ∀ f, T (fun x => c • f x) = fun x => c • T f x) (f : Mx k r → E) :
    L.foldl (fun h T => T h) (fun x => c • f x) = fun x => c • L.foldl (fun h T => T h) f x := by sorry

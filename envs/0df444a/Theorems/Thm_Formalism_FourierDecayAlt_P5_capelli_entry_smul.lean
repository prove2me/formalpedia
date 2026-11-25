-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_capelli_entry_smul
-- name    : Formalism.FourierDecayAlt.P5.capelli_entry_smul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:56:40.817545+00:00
-- url     : https://prove2.me/theorems/b1c7ab2e-d118-4ab0-a643-9c9874797fd0
-- title:
--   P5: capelli entry smul
-- statement:
--   The P5 construction uses the capelli entry smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtFsvOther.lean#L104-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasFDerivAtFsvOther.lean#L104-L113

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtFsvOther
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate ContDiff
open Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P5.capelli_entry_smul {t : ℕ} (pos : Fin t → Fin (2 * r + k + 1)) (u : ℂ) (a a' β β' : Mx k r → Fin t → ℂ) :
    SmulC (E := E) (chat2L (EH k r) pos u a a' β β') := by sorry

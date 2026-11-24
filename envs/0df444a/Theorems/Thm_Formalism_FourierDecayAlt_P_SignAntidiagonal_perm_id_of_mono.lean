-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_perm_id_of_mono
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.perm_id_of_mono
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:06:44.667947+00:00
-- url     : https://prove2.me/theorems/1cfb74d6-0246-4d29-a6b3-20447117a8f1
-- title:
--   Sign Antidiagonal: perm id of mono
-- statement:
--   The Sign Antidiagonal construction uses the perm id of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeadingTermIdentity.lean#L9-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeadingTermIdentity.lean#L9-L23

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlMonoConst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeadingTermIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.perm_id_of_mono {m : ℕ} (τ : Equiv.Perm (Fin m)) (h : StrictMono (fun l => (τ l).val)) : τ = 1 := by sorry

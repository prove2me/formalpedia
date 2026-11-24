-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_uniq_mono
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.uniq_mono
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:51:44.740982+00:00
-- url     : https://prove2.me/theorems/a4379dcc-897c-49b1-a901-6447dfa220d2
-- title:
--   Sign Antidiagonal: uniq mono
-- statement:
--   The Sign Antidiagonal construction uses the uniq mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AAvCongr.lean#L47-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AAvCongr.lean#L47-L54

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPeelingMinorMemIdeal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AAvCongr
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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.uniq_mono {α : Type} [LinearOrder α] {m : ℕ} (e c : Fin m → α) (he : StrictMono e) (hc : StrictMono c)
    (hS : ∀ l, c l ∈ Set.range e) : c = e := by sorry

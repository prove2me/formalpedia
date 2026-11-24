-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_uniq_key
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.uniq_key
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:53:28.882802+00:00
-- url     : https://prove2.me/theorems/0ff3cfff-547b-4ae8-817a-beca0a1a392a
-- title:
--   Sign Antidiagonal: uniq key
-- statement:
--   The Sign Antidiagonal construction uses the uniq key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AAvCongr.lean#L56-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AAvCongr.lean#L56-L61

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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.uniq_key {N m : ℕ} (key : Fin N → ℕ) (hkey : Function.Injective key) (e c : Fin m → Fin N)
    (he : StrictMono (fun l => key (e l))) (hc : StrictMono (fun l => key (c l)))
    (hS : ∀ l, c l ∈ Set.range e) : c = e := by sorry

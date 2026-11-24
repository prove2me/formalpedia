-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_mono_omit
-- name    : Formalism.FourierDecayAlt.P.PBG.mono_omit
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:39:12.644276+00:00
-- url     : https://prove2.me/theorems/5a0b8f86-aff9-4fc6-8a11-2925d25f3ff0
-- title:
--   PBG: mono omit
-- statement:
--   The PBG construction uses the mono omit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHead.lean#L10-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBGHead.lean#L10-L33

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainFirstIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHead
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal

theorem Formalism.FourierDecayAlt.P.PBG.mono_omit {k r m : ℕ} (hm : m + 1 ≤ r) (c : Fin m → Fin (2 * r + k + 1)) (hc : StrictMono c)
    (hlt : ∀ l, (c l).val < m + 1) : ∃ l0 : Fin (m + 1), c = xR k r (m + 1) hm ∘ l0.succAbove := by sorry
